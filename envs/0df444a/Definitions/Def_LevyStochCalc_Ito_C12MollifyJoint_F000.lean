-- Prove2me | Definitions.Def_LevyStochCalc_Ito_C12MollifyJoint_F000
-- name    : LevyStochCalc_Ito_C12MollifyJoint_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:02:15.564791+00:00
-- url     : https://prove2.me/theorems/e005c9cd-0145-4e52-9bc7-ae838eb96ccf
-- title:
--   Source declarations: LevyStochCalc.Ito.C12MollifyJoint
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.C12MollifyJoint. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_C12Mollify_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Joint mollification in time and state of a function of time and state

For a function `u : ℝ → (Fin n → ℝ) → ℝ` of time and state and a smooth compactly supported bump
`ρ` on the product `ℝ × (Fin n → ℝ)`, the joint mollification
`mollifyJoint u ρ t x = ∫ p, ρ(p) u(t - p₁, x - p₂) dp` averages `u` over a neighbourhood of
`(t, x)` of diameter the outer radius of `ρ`. As a function of time and state it is the
convolution of the normalised bump with `Function.uncurry u` on the product, so for a continuous
`u` it is `C^N` jointly in time and state for every `N`, in particular of class `C^{1,2}`; the
mollification in time alone of a `C^{1,2}` function is only known to be `C^{1,2}`, its joint `C²`
regularity not being available from continuity of the partial derivatives.

For a `C^{1,2}` function `u` the time derivative, the gradient and the Hessian of the joint
mollification are the joint mollifications of the time derivative, the gradient and the Hessian
of `u`; uniform bounds on those derivatives therefore pass to the mollification, and along a
family of bumps whose outer radii tend to `0` each of them converges pointwise to its
counterpart for `u`.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.mollifyJoint_eq_convolution` — the joint mollification is a
  convolution on `ℝ × (Fin n → ℝ)`.
* `LevyStochCalc.Ito.JumpFormula.contDiff_uncurry_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.isC12_mollifyJoint` — the joint mollification of a jointly
  continuous function is `C^N` jointly in time and state, hence of class `C^{1,2}`.
* `LevyStochCalc.Ito.JumpFormula.timeDeriv_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.gradient_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.hessian_mollifyJoint` — the time derivative, the gradient and
  the Hessian of the joint mollification of a `C^{1,2}` function are the joint mollifications of
  the time derivative, the gradient and the Hessian of that function.
* `LevyStochCalc.Ito.JumpFormula.abs_mollifyJoint_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_timeDeriv_mollifyJoint_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_gradient_mollifyJoint_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_hessian_mollifyJoint_le` — uniform bounds on a function and
  on its derivatives pass to the joint mollification.
* `LevyStochCalc.Ito.JumpFormula.tendsto_mollifyJoint` — pointwise convergence of the joint
  mollification along a family of bumps whose outer radii tend to `0`, with the corresponding
  statements for the time derivative, the gradient and the Hessian.
* `LevyStochCalc.Ito.JumpFormula.exists_seq_bump_rOut_tendsto_zero` — a sequence of bumps on
  `ℝ × (Fin n → ℝ)` whose outer radii tend to `0`.
-/

open MeasureTheory Filter Topology
open scoped Convolution

namespace LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- The volume measure on the product of the time line with the state space is an additive Haar
measure. -/
theorem isAddHaarMeasure_volume_time_state (n : ℕ) :
    (volume : Measure (ℝ × (Fin n → ℝ))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _
/-- Mollification in time and state of `u : ℝ → (Fin n → ℝ) → ℝ` against a bump `ρ` on
`ℝ × (Fin n → ℝ)`, normalised for the volume measure:
`mollifyJoint u ρ t x = ∫ p, ρ(p) u(t - p₁, x - p₂) dp`. -/
noncomputable def mollifyJoint (u : ℝ → (Fin n → ℝ) → ℝ)
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ p : ℝ × (Fin n → ℝ), ρ.normed volume p * u (t - p.1) (x - p.2)
/-- As a function on `ℝ × (Fin n → ℝ)` the joint mollification is the convolution of the
normalised bump with `u`. -/
theorem mollifyJoint_eq_convolution (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) :
    Function.uncurry (mollifyJoint u ρ)
      = ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Function.uncurry u := by
  funext p
  simp only [Function.uncurry_def, mollifyJoint, convolution_lsmul, smul_eq_mul, Prod.fst_sub,
    Prod.snd_sub]
/-- The joint mollification of a jointly continuous function of time and state is `C^N` jointly
in time and state for every `N`, the derivatives falling on the bump. -/
theorem contDiff_uncurry_mollifyJoint {N : ℕ∞} (hu : Continuous (Function.uncurry u))
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) :
    ContDiff ℝ (N : WithTop ℕ∞) (Function.uncurry (mollifyJoint u ρ)) := by
  haveI := isAddHaarMeasure_volume_time_state n
  rw [mollifyJoint_eq_convolution]
  exact HasCompactSupport.contDiff_convolution_left _ ρ.hasCompactSupport_normed
    ρ.contDiff_normed hu.locallyIntegrable
/-- The joint mollification of a jointly continuous function of time and state is of class
`C^{1,2}`. -/
theorem isC12_mollifyJoint (hu : Continuous (Function.uncurry u))
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) : IsC12 (mollifyJoint u ρ) :=
  IsC12.of_contDiff (contDiff_uncurry_mollifyJoint (N := 2) hu ρ)
/-- The integrand of the joint mollification is continuous in the integration variable. -/
theorem continuous_mollifyJoint_integrand (hu : Continuous (Function.uncurry u))
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ) (x : Fin n → ℝ) :
    Continuous fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p * u (t - p.1) (x - p.2) := by
  have h : Continuous fun p : ℝ × (Fin n → ℝ) => Function.uncurry u ((t, x) - p) :=
    hu.comp (continuous_const.sub continuous_id)
  exact ρ.continuous_normed.mul h
/-- The integrand of the joint mollification has compact support. -/
theorem hasCompactSupport_mollifyJoint_integrand (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ)))
    (t : ℝ) (x : Fin n → ℝ) :
    HasCompactSupport fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p * u (t - p.1) (x - p.2) :=
  ρ.hasCompactSupport_normed.mul_right
/-- The integrand of the joint mollification is integrable. -/
theorem integrable_mollifyJoint_integrand (hu : Continuous (Function.uncurry u))
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ) (x : Fin n → ℝ) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p * u (t - p.1) (x - p.2)) volume :=
  (continuous_mollifyJoint_integrand hu ρ t x).integrable_of_hasCompactSupport
    (hasCompactSupport_mollifyJoint_integrand ρ t x)
/-- A continuous function on time and state, evaluated at arguments shifted by the support of a
bump on `ℝ × (Fin n → ℝ)` and taken over a unit neighbourhood of a point, is dominated by a
multiple of the normalised bump. -/
theorem exists_bound_bump_joint {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) {g : ℝ × (Fin n → ℝ) → F} (hg : Continuous g)
    (t : ℝ) (x : Fin n → ℝ) :
    ∃ M : ℝ, ∀ p : ℝ × (Fin n → ℝ), ∀ τ ∈ Set.Ioo (t - 1) (t + 1), ∀ z ∈ Metric.ball x 1,
      ‖ρ.normed volume p • g (τ - p.1, z - p.2)‖ ≤ ρ.normed volume p * M := by
  have hKc : IsCompact (Set.Icc (t - 1 - ρ.rOut) (t + 1 + ρ.rOut) ×ˢ
      Metric.closedBall x (1 + ρ.rOut)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨M, fun p τ hτ z hz => ?_⟩
  rcases eq_or_lt_of_le (ρ.nonneg_normed p) with hr | hr
  · rw [← hr]
    simp
  · have hrb : ‖p‖ < ρ.rOut := by
      have hmem : p ∈ Metric.ball (0 : ℝ × (Fin n → ℝ)) ρ.rOut := by
        rw [← ρ.support_normed_eq (μ := volume)]
        exact hr.ne'
      simpa [mem_ball_zero_iff] using hmem
    have hp1 : |p.1| < ρ.rOut := lt_of_le_of_lt (le_trans (le_of_eq rfl) (norm_fst_le p)) hrb
    have hp2 : ‖p.2‖ < ρ.rOut := lt_of_le_of_lt (norm_snd_le p) hrb
    have hmem : (τ - p.1, z - p.2) ∈ Set.Icc (t - 1 - ρ.rOut) (t + 1 + ρ.rOut) ×ˢ
        Metric.closedBall x (1 + ρ.rOut) := by
      obtain ⟨hl, hu'⟩ := Set.mem_Ioo.mp hτ
      obtain ⟨ha, hb⟩ := abs_lt.mp hp1
      refine ⟨Set.mem_Icc.mpr ⟨by linarith, by linarith⟩, ?_⟩
      have hzx : dist z x < 1 := Metric.mem_ball.mp hz
      have hshift : dist (z - p.2) z = ‖p.2‖ := by simp
      have htri : dist (z - p.2) x ≤ dist (z - p.2) z + dist z x := dist_triangle _ _ _
      rw [hshift] at htri
      exact Metric.mem_closedBall.mpr (by linarith)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg_normed p)]
    exact mul_le_mul_of_nonneg_left (hM _ hmem) (ρ.nonneg_normed p)
/-- The joint mollification of a `C^{1,2}` function is differentiable in time, with derivative
the joint mollification of the time derivative. -/
theorem hasDerivAt_time_mollifyJoint (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ)))
    (t₀ : ℝ) (x : Fin n → ℝ) :
    HasDerivAt (fun t => mollifyJoint u ρ t x) (mollifyJoint (timeDeriv u) ρ t₀ x) t₀ := by
  have hdu : Continuous (Function.uncurry (timeDeriv u)) := hu.continuous_timeDeriv
  obtain ⟨M, hM⟩ := exists_bound_bump_joint ρ hdu t₀ x
  have hs : Set.Ioo (t₀ - 1) (t₀ + 1) ∈ 𝓝 t₀ :=
    isOpen_Ioo.mem_nhds (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
  have hdiff : ∀ᵐ p : ℝ × (Fin n → ℝ), ∀ τ ∈ Set.Ioo (t₀ - 1) (t₀ + 1),
      HasDerivAt (fun s : ℝ => ρ.normed volume p * u (s - p.1) (x - p.2))
        (ρ.normed volume p * timeDeriv u (τ - p.1) (x - p.2)) τ := by
    refine Eventually.of_forall fun p τ _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => u (s - p.1) (x - p.2))
        (timeDeriv u (τ - p.1) (x - p.2)) τ := by
      have h2 := (hu.hasTimeDeriv (τ - p.1) (x - p.2)).comp τ ((hasDerivAt_id τ).sub_const p.1)
      simpa [Function.comp_def] using h2
    exact h1.const_mul (ρ.normed volume p)
  have hbound : ∀ᵐ p : ℝ × (Fin n → ℝ), ∀ τ ∈ Set.Ioo (t₀ - 1) (t₀ + 1),
      ‖ρ.normed volume p * timeDeriv u (τ - p.1) (x - p.2)‖ ≤ ρ.normed volume p * M :=
    Eventually.of_forall fun p τ hτ => by
      simpa using hM p τ hτ x (Metric.mem_ball_self one_pos)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s : ℝ => fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p * u (s - p.1) (x - p.2))
    (F' := fun s : ℝ => fun p : ℝ × (Fin n → ℝ) =>
      ρ.normed volume p * timeDeriv u (s - p.1) (x - p.2))
    (bound := fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p * M) hs
    (Eventually.of_forall fun s =>
      (continuous_mollifyJoint_integrand hu.continuous ρ s x).aestronglyMeasurable)
    (integrable_mollifyJoint_integrand hu.continuous ρ t₀ x)
    (continuous_mollifyJoint_integrand hdu ρ t₀ x).aestronglyMeasurable hbound
    (ρ.integrable_normed.mul_const M) hdiff
  exact hmain.2
/-- The time derivative of the joint mollification of a `C^{1,2}` function is the joint
mollification of its time derivative. -/
theorem timeDeriv_mollifyJoint (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ)
    (x : Fin n → ℝ) :
    timeDeriv (mollifyJoint u ρ) t x = mollifyJoint (timeDeriv u) ρ t x :=
  (hasDerivAt_time_mollifyJoint hu ρ t x).deriv
/-- The state-derivative integrand of the joint mollification is continuous in the integration
variable. -/
theorem continuous_mollifyJoint_fderiv_integrand (hu : IsC12 u)
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ) (z : Fin n → ℝ) :
    Continuous fun p : ℝ × (Fin n → ℝ) =>
      ρ.normed volume p • fderiv ℝ (u (t - p.1)) (z - p.2) := by
  have h : Continuous fun p : ℝ × (Fin n → ℝ) =>
      fderiv ℝ (u (((t, z) - p).1)) (((t, z) - p).2) :=
    (continuous_fderiv_state hu).comp (continuous_const.sub continuous_id)
  exact ρ.continuous_normed.smul h
/-- The state-derivative integrand of the joint mollification is integrable. -/
theorem integrable_mollifyJoint_fderiv_integrand (hu : IsC12 u)
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ) (z : Fin n → ℝ) :
    Integrable (fun p : ℝ × (Fin n → ℝ) =>
      ρ.normed volume p • fderiv ℝ (u (t - p.1)) (z - p.2)) volume :=
  (continuous_mollifyJoint_fderiv_integrand hu ρ t z).integrable_of_hasCompactSupport
    ρ.hasCompactSupport_normed.smul_right
/-- The joint mollification of a `C^{1,2}` function is differentiable in the state, with state
derivative the integral of the mollified state derivatives. -/
theorem hasFDerivAt_state_mollifyJoint (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ)))
    (t : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (mollifyJoint u ρ t)
      (∫ p : ℝ × (Fin n → ℝ), ρ.normed volume p • fderiv ℝ (u (t - p.1)) (x - p.2)) x := by
  obtain ⟨M, hM⟩ := exists_bound_bump_joint ρ (continuous_fderiv_state hu) t x
  have hbound : ∀ᵐ p : ℝ × (Fin n → ℝ), ∀ z ∈ Metric.ball x 1,
      ‖ρ.normed volume p • fderiv ℝ (u (t - p.1)) (z - p.2)‖ ≤ ρ.normed volume p * M :=
    Eventually.of_forall fun p z hz => by
      simpa using hM p t (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) z hz
  have hdiff : ∀ᵐ p : ℝ × (Fin n → ℝ), ∀ z ∈ Metric.ball x 1,
      HasFDerivAt (fun y : Fin n → ℝ => ρ.normed volume p * u (t - p.1) (y - p.2))
        (ρ.normed volume p • fderiv ℝ (u (t - p.1)) (z - p.2)) z := by
    refine Eventually.of_forall fun p z _ => ?_
    have h0 : HasFDerivAt (u (t - p.1)) (fderiv ℝ (u (t - p.1)) (z - p.2)) (z - p.2) :=
      (((hu.contDiff_section (t - p.1)).differentiable (by norm_num)) (z - p.2)).hasFDerivAt
    have h1 := h0.comp z ((hasFDerivAt_id z).sub_const p.2)
    simpa using h1.const_mul (ρ.normed volume p)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z : Fin n → ℝ => fun p : ℝ × (Fin n → ℝ) =>
      ρ.normed volume p * u (t - p.1) (z - p.2))
    (F' := fun z : Fin n → ℝ => fun p : ℝ × (Fin n → ℝ) =>
      ρ.normed volume p • fderiv ℝ (u (t - p.1)) (z - p.2))
    (bound := fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p * M)
    (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun z =>
      (continuous_mollifyJoint_integrand hu.continuous ρ t z).aestronglyMeasurable)
    (integrable_mollifyJoint_integrand hu.continuous ρ t x)
    (continuous_mollifyJoint_fderiv_integrand hu ρ t x).aestronglyMeasurable hbound
    (ρ.integrable_normed.mul_const M) hdiff
/-- The gradient of the joint mollification of a `C^{1,2}` function is the joint mollification
of its gradient. -/
theorem gradient_mollifyJoint (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    gradient (mollifyJoint u ρ) t x i = mollifyJoint (fun s y => gradient u s y i) ρ t x := by
  simp only [gradient, (hasFDerivAt_state_mollifyJoint hu ρ t x).fderiv]
  rw [ContinuousLinearMap.integral_apply (integrable_mollifyJoint_fderiv_integrand hu ρ t x)]
  simp only [mollifyJoint, smul_apply, smul_eq_mul]
/-- The second-derivative integrand of the joint mollification is continuous in the integration
variable. -/
theorem continuous_mollifyJoint_hessian_integrand (hu : IsC12 u)
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ) (z : Fin n → ℝ) (i : Fin n) :
    Continuous fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p •
      fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - p.1) y i) (z - p.2) := by
  have h : Continuous fun p : ℝ × (Fin n → ℝ) =>
      fderiv ℝ (fun y : Fin n → ℝ => gradient u (((t, z) - p).1) y i) (((t, z) - p).2) :=
    (continuous_fderiv_gradient hu i).comp (continuous_const.sub continuous_id)
  exact ρ.continuous_normed.smul h
/-- The second-derivative integrand of the joint mollification is integrable. -/
theorem integrable_mollifyJoint_hessian_integrand (hu : IsC12 u)
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ) (z : Fin n → ℝ) (i : Fin n) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p •
      fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - p.1) y i) (z - p.2)) volume :=
  (continuous_mollifyJoint_hessian_integrand hu ρ t z i).integrable_of_hasCompactSupport
    ρ.hasCompactSupport_normed.smul_right
/-- The joint mollification of a gradient coordinate of a `C^{1,2}` function is differentiable
in the state, with state derivative the integral of the mollified second derivatives. -/
theorem hasFDerivAt_state_mollifyJoint_gradient (hu : IsC12 u)
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    HasFDerivAt (mollifyJoint (fun s y => gradient u s y i) ρ t)
      (∫ p : ℝ × (Fin n → ℝ), ρ.normed volume p •
        fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - p.1) y i) (x - p.2)) x := by
  have hg : Continuous (Function.uncurry fun s (y : Fin n → ℝ) => gradient u s y i) :=
    hu.continuous_gradient i
  obtain ⟨M, hM⟩ := exists_bound_bump_joint ρ (continuous_fderiv_gradient hu i) t x
  have hbound : ∀ᵐ p : ℝ × (Fin n → ℝ), ∀ z ∈ Metric.ball x 1,
      ‖ρ.normed volume p • fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - p.1) y i) (z - p.2)‖
        ≤ ρ.normed volume p * M :=
    Eventually.of_forall fun p z hz => by
      simpa using hM p t (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) z hz
  have hdiff : ∀ᵐ p : ℝ × (Fin n → ℝ), ∀ z ∈ Metric.ball x 1,
      HasFDerivAt (fun y : Fin n → ℝ => ρ.normed volume p * gradient u (t - p.1) (y - p.2) i)
        (ρ.normed volume p •
          fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - p.1) y i) (z - p.2)) z := by
    refine Eventually.of_forall fun p z _ => ?_
    have h0 : HasFDerivAt (fun y : Fin n → ℝ => gradient u (t - p.1) y i)
        (fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - p.1) y i) (z - p.2)) (z - p.2) :=
      (differentiable_gradient_state hu (t - p.1) i (z - p.2)).hasFDerivAt
    have h1 := h0.comp z ((hasFDerivAt_id z).sub_const p.2)
    simpa using h1.const_mul (ρ.normed volume p)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z : Fin n → ℝ => fun p : ℝ × (Fin n → ℝ) =>
      ρ.normed volume p * gradient u (t - p.1) (z - p.2) i)
    (F' := fun z : Fin n → ℝ => fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p •
      fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - p.1) y i) (z - p.2))
    (bound := fun p : ℝ × (Fin n → ℝ) => ρ.normed volume p * M)
    (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun z =>
      (continuous_mollifyJoint_integrand hg ρ t z).aestronglyMeasurable)
    (integrable_mollifyJoint_integrand hg ρ t x)
    (continuous_mollifyJoint_hessian_integrand hu ρ t x i).aestronglyMeasurable hbound
    (ρ.integrable_normed.mul_const M) hdiff
/-- The Hessian of the joint mollification of a `C^{1,2}` function is the joint mollification of
its Hessian. -/
theorem hessian_mollifyJoint (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) (t : ℝ)
    (x : Fin n → ℝ) (i j : Fin n) :
    hessian (mollifyJoint u ρ) t x i j = mollifyJoint (fun s y => hessian u s y i j) ρ t x := by
  have hfun : (fun y : Fin n → ℝ => fderiv ℝ (mollifyJoint u ρ t) y (Pi.single i 1))
      = mollifyJoint (fun s z => gradient u s z i) ρ t :=
    funext fun y => gradient_mollifyJoint hu ρ t y i
  simp only [hessian, hfun, (hasFDerivAt_state_mollifyJoint_gradient hu ρ t x i).fderiv]
  rw [ContinuousLinearMap.integral_apply (integrable_mollifyJoint_hessian_integrand hu ρ t x i)]
  simp only [mollifyJoint, smul_apply, smul_eq_mul, gradient]
/-- The joint mollification of a function bounded by `K` is bounded by `K`. -/
theorem abs_mollifyJoint_le (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) {K : ℝ}
    (hK : ∀ s y, |u s y| ≤ K) (t : ℝ) (x : Fin n → ℝ) : |mollifyJoint u ρ t x| ≤ K := by
  have hbound : ∀ᵐ p : ℝ × (Fin n → ℝ),
      ‖ρ.normed volume p * u (t - p.1) (x - p.2)‖ ≤ ρ.normed volume p * K :=
    Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ρ.nonneg_normed p)]
      exact mul_le_mul_of_nonneg_left (hK _ _) (ρ.nonneg_normed p)
  have hint : ∫ p : ℝ × (Fin n → ℝ), ρ.normed volume p * K = K := by
    rw [integral_mul_const, ρ.integral_normed, one_mul]
  have h := norm_integral_le_of_norm_le (ρ.integrable_normed.mul_const K) hbound
  rw [hint] at h
  simpa [mollifyJoint, Real.norm_eq_abs] using h
/-- A uniform bound on the time derivative passes to the joint mollification. -/
theorem abs_timeDeriv_mollifyJoint_le (hu : IsC12 u)
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) {K₀ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀) :
    ∀ t x, |timeDeriv (mollifyJoint u ρ) t x| ≤ K₀ := by
  intro t x
  rw [timeDeriv_mollifyJoint hu]
  exact abs_mollifyJoint_le ρ hK₀ t x
/-- A uniform coordinatewise bound on the gradient passes to the joint mollification. -/
theorem abs_gradient_mollifyJoint_le (hu : IsC12 u)
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) {K₁ : ℝ} (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) :
    ∀ t x i, |gradient (mollifyJoint u ρ) t x i| ≤ K₁ := by
  intro t x i
  rw [gradient_mollifyJoint hu]
  exact abs_mollifyJoint_le ρ (fun s y => hK₁ s y i) t x
/-- A uniform entrywise bound on the Hessian passes to the joint mollification. -/
theorem abs_hessian_mollifyJoint_le (hu : IsC12 u)
    (ρ : ContDiffBump (0 : ℝ × (Fin n → ℝ))) {K₂ : ℝ}
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂) :
    ∀ t x i j, |hessian (mollifyJoint u ρ) t x i j| ≤ K₂ := by
  intro t x i j
  rw [hessian_mollifyJoint hu]
  exact abs_mollifyJoint_le ρ (fun s y => hK₂ s y i j) t x
/-- Along a family of bumps whose outer radii tend to `0` the joint mollification of a jointly
continuous function converges to that function pointwise. -/
theorem tendsto_mollifyJoint {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ × (Fin n → ℝ))}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hu : Continuous (Function.uncurry u)) (t : ℝ)
    (x : Fin n → ℝ) : Tendsto (fun i => mollifyJoint u (φ i) t x) l (𝓝 (u t x)) := by
  haveI := isAddHaarMeasure_volume_time_state n
  have h : ∀ i, mollifyJoint u (φ i) t x
      = ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Function.uncurry u)
        (t, x) := fun i => congrFun (mollifyJoint_eq_convolution (φ i)) (t, x)
  simp only [h]
  exact ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hu (t, x)
/-- Along a family of bumps whose outer radii tend to `0` the time derivative of the joint
mollification of a `C^{1,2}` function converges to its time derivative pointwise. -/
theorem tendsto_timeDeriv_mollifyJoint {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ × (Fin n → ℝ))}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hu : IsC12 u) (t : ℝ) (x : Fin n → ℝ) :
    Tendsto (fun i => timeDeriv (mollifyJoint u (φ i)) t x) l (𝓝 (timeDeriv u t x)) := by
  simp only [timeDeriv_mollifyJoint hu]
  exact tendsto_mollifyJoint (u := timeDeriv u) hφ hu.continuous_timeDeriv t x
/-- Along a family of bumps whose outer radii tend to `0` the gradient of the joint mollification
of a `C^{1,2}` function converges to its gradient pointwise. -/
theorem tendsto_gradient_mollifyJoint {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ × (Fin n → ℝ))}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hu : IsC12 u) (t : ℝ) (x : Fin n → ℝ)
    (i : Fin n) :
    Tendsto (fun k => gradient (mollifyJoint u (φ k)) t x i) l (𝓝 (gradient u t x i)) := by
  simp only [gradient_mollifyJoint hu]
  exact tendsto_mollifyJoint (u := fun s y => gradient u s y i) hφ
    (hu.continuous_gradient i) t x
/-- Along a family of bumps whose outer radii tend to `0` the Hessian of the joint mollification
of a `C^{1,2}` function converges to its Hessian pointwise. -/
theorem tendsto_hessian_mollifyJoint {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ × (Fin n → ℝ))}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hu : IsC12 u) (t : ℝ) (x : Fin n → ℝ)
    (i j : Fin n) :
    Tendsto (fun k => hessian (mollifyJoint u (φ k)) t x i j) l (𝓝 (hessian u t x i j)) := by
  simp only [hessian_mollifyJoint hu]
  exact tendsto_mollifyJoint (u := fun s y => hessian u s y i j) hφ
    (hu.continuous_hessian i j) t x
/-- A sequence of bumps on `ℝ × (Fin n → ℝ)` whose outer radii tend to `0`. -/
theorem exists_seq_bump_rOut_tendsto_zero (n : ℕ) :
    ∃ φ : ℕ → ContDiffBump (0 : ℝ × (Fin n → ℝ)),
      Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
  refine ⟨fun k => ⟨1 / ((k : ℝ) + 2), 1 / ((k : ℝ) + 1), by positivity, ?_⟩, ?_⟩
  · have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : ((k : ℝ) + 1) < (k : ℝ) + 2 := by linarith
    exact one_div_lt_one_div_of_lt h1 h2
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
end LevyStochCalc.Ito.JumpFormula


