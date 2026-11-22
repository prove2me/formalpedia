-- Prove2me | Definitions.Def_LevyStochCalc_Ito_C12_F000
-- name    : LevyStochCalc_Ito_C12_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:50:40.745215+00:00
-- url     : https://prove2.me/theorems/54318ee3-bf11-4eeb-9b1c-7bba4d0e56f3
-- title:
--   Source declarations: LevyStochCalc.Ito.C12
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.C12. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuity_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaTaylorBounds_F000
import Mathlib.Analysis.Calculus.Deriv.Abs

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The class `C^{1,2}` of functions of time and state

The Itô–Lévy formula is stated for a function `u : ℝ → (Fin n → ℝ) → ℝ` of time and state that is
once continuously differentiable in time and twice continuously differentiable in state, the
class `C^{1,2}`. The predicate `IsC12` records that regularity through the vocabulary of the
formula itself: a time derivative `timeDeriv u`, a state gradient `gradient u` and a state
Hessian `hessian u`, each jointly continuous in time and state, together with joint continuity of
`u` and `C²` regularity of every state section `u s`.

Joint `C²` regularity of `Function.uncurry u` implies `IsC12 u`, and the implication is strict:
for `g t = t |t|`, which is differentiable with continuous derivative `2 |t|` but not twice
differentiable at `0`, the function `(t, x) ↦ g t · x₀²` is `C^{1,2}` yet not jointly `C²`.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.IsC12` — the `C^{1,2}` regularity predicate.
* `LevyStochCalc.Ito.JumpFormula.IsC12.of_contDiff` — joint `C²` regularity implies `C^{1,2}`.
* `LevyStochCalc.Ito.JumpFormula.isC12_sampleC12`,
  `LevyStochCalc.Ito.JumpFormula.not_contDiff_uncurry_sampleC12` — the function
  `(t, x) ↦ t |t| x₀²` is `C^{1,2}` and is not jointly `C²`.
-/

open Filter Topology

namespace LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- `IsC12 u` states that `u : ℝ → (Fin n → ℝ) → ℝ` is of class `C^{1,2}`: continuous jointly in
time and state, differentiable in time with jointly continuous time derivative, and `C²` in the
state with jointly continuous gradient and Hessian. -/
structure IsC12 (u : ℝ → (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous (Function.uncurry u)
  hasTimeDeriv : ∀ s x, HasDerivAt (fun t => u t x) (timeDeriv u s x) s
  continuous_timeDeriv : Continuous fun p : ℝ × (Fin n → ℝ) => timeDeriv u p.1 p.2
  contDiff_section : ∀ s, ContDiff ℝ 2 (u s)
  continuous_gradient : ∀ i, Continuous fun p : ℝ × (Fin n → ℝ) => gradient u p.1 p.2 i
  continuous_hessian : ∀ i j, Continuous fun p : ℝ × (Fin n → ℝ) => hessian u p.1 p.2 i j
/-- A function of time and state that is `C²` jointly is of class `C^{1,2}`. -/
theorem IsC12.of_contDiff (hu : ContDiff ℝ 2 (Function.uncurry u)) : IsC12 u where
  continuous := hu.continuous
  hasTimeDeriv := fun s x =>
    (((hu.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)) s).hasDerivAt
  continuous_timeDeriv := JumpFormula.continuous_timeDeriv hu
  contDiff_section := fun s => contDiff_state_section hu s
  continuous_gradient := fun i => continuous_gradient_uncurry hu i
  continuous_hessian := fun i j => JumpFormula.continuous_hessian hu i j
section Sample

/-- The function `t ↦ t |t|` is differentiable with derivative `2 |t|`. -/
theorem hasDerivAt_mul_abs (s : ℝ) : HasDerivAt (fun t : ℝ => t * |t|) (2 * |s|) s := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have hev : (fun t : ℝ => t * |t|) =ᶠ[𝓝 s] fun t : ℝ => -t ^ 2 := by
      filter_upwards [isOpen_Iio.eventually_mem (Set.mem_Iio.mpr hs)] with t ht
      rw [abs_of_neg (Set.mem_Iio.mp ht)]; ring
    have h' : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    have h : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * s)) s := h'.neg
    have he : -(2 * s) = 2 * |s| := by rw [abs_of_neg hs]; ring
    rw [hev.hasDerivAt_iff, ← he]
    exact h
  · subst hs
    have h0 : (2 : ℝ) * |(0 : ℝ)| = 0 := by simp
    rw [hasDerivAt_iff_tendsto_slope, h0]
    have hcongr : (fun t : ℝ => |t|) =ᶠ[𝓝[≠] (0 : ℝ)] slope (fun t : ℝ => t * |t|) 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      rw [slope_def_field]
      simp only [abs_zero, mul_zero, sub_zero]
      rw [mul_comm, mul_div_assoc, div_self ht', mul_one]
    refine Filter.Tendsto.congr' hcongr ?_
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · have hev : (fun t : ℝ => t * |t|) =ᶠ[𝓝 s] fun t : ℝ => t ^ 2 := by
      filter_upwards [isOpen_Ioi.eventually_mem (Set.mem_Ioi.mpr hs)] with t ht
      rw [abs_of_pos (Set.mem_Ioi.mp ht)]; ring
    have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    have he : (2 : ℝ) * s = 2 * |s| := by rw [abs_of_pos hs]
    rw [hev.hasDerivAt_iff, ← he]
    exact h
/-- The function `(t, x) ↦ t |t| x₀²` of time and one-dimensional state. -/
noncomputable def sampleC12 (t : ℝ) (x : Fin 1 → ℝ) : ℝ := t * |t| * x 0 ^ 2
/-- The state derivative of `sampleC12 t` is `2 t |t| x₀` times the coordinate projection. -/
theorem hasFDerivAt_sampleC12 (t : ℝ) (x : Fin 1 → ℝ) :
    HasFDerivAt (sampleC12 t)
      ((2 * (t * |t|) * x 0) •
        (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ)) x := by
  have hf : HasFDerivAt (fun y : Fin 1 → ℝ => y 0)
      (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x 0) (x 0) := by
    simpa using hasDerivAt_pow 2 (x 0)
  have hg : HasDerivAt (fun y : ℝ => t * |t| * y ^ 2) (2 * (t * |t|) * x 0) (x 0) := by
    have h := HasDerivAt.const_mul (t * |t|) hp
    have he : t * |t| * (2 * x 0) = 2 * (t * |t|) * x 0 := by ring
    rwa [he] at h
  have hcomp : HasFDerivAt ((fun y : ℝ => t * |t| * y ^ 2) ∘ fun y : Fin 1 → ℝ => y 0)
      ((2 * (t * |t|) * x 0) •
        (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ)) x :=
    hg.comp_hasFDerivAt x hf
  exact hcomp
/-- Time derivative of `(t, x) ↦ t |t| x₀²`. -/
theorem timeDeriv_sampleC12 (s : ℝ) (x : Fin 1 → ℝ) :
    timeDeriv sampleC12 s x = 2 * |s| * x 0 ^ 2 :=
  ((hasDerivAt_mul_abs s).mul_const (x 0 ^ 2)).deriv
/-- Gradient of `(t, x) ↦ t |t| x₀²`. -/
theorem gradient_sampleC12 (t : ℝ) (x : Fin 1 → ℝ) (i : Fin 1) :
    gradient sampleC12 t x i = 2 * (t * |t|) * x 0 := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [gradient, (hasFDerivAt_sampleC12 t x).fderiv, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
/-- Hessian of `(t, x) ↦ t |t| x₀²`. -/
theorem hessian_sampleC12 (t : ℝ) (x : Fin 1 → ℝ) (i j : Fin 1) :
    hessian sampleC12 t x i j = 2 * (t * |t|) := by
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  subst hi
  subst hj
  have hfun : (fun y : Fin 1 → ℝ => fderiv ℝ (sampleC12 t) y (Pi.single (0 : Fin 1) 1))
      = fun y : Fin 1 → ℝ => 2 * (t * |t|) * y 0 :=
    funext fun y => gradient_sampleC12 t y 0
  have hd : HasFDerivAt (fun y : Fin 1 → ℝ => 2 * (t * |t|) * y 0)
      ((2 * (t * |t|)) • (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ)) x :=
    HasFDerivAt.const_mul
      (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).hasFDerivAt _
  simp only [hessian, hfun, hd.fderiv, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
/-- The function `(t, x) ↦ t |t| x₀²` is of class `C^{1,2}`. -/
theorem isC12_sampleC12 : IsC12 sampleC12 where
  continuous := by
    have h : Function.uncurry sampleC12
        = fun p : ℝ × (Fin 1 → ℝ) => p.1 * |p.1| * p.2 0 ^ 2 := rfl
    rw [h]
    exact (continuous_fst.mul continuous_fst.abs).mul
      (((continuous_apply (0 : Fin 1)).comp continuous_snd).pow 2)
  hasTimeDeriv := by
    intro s x
    have h : HasDerivAt (fun t : ℝ => sampleC12 t x) (2 * |s| * x 0 ^ 2) s :=
      (hasDerivAt_mul_abs s).mul_const (x 0 ^ 2)
    rw [timeDeriv_sampleC12 s x]
    exact h
  continuous_timeDeriv := by
    have h : (fun p : ℝ × (Fin 1 → ℝ) => timeDeriv sampleC12 p.1 p.2)
        = fun p : ℝ × (Fin 1 → ℝ) => 2 * |p.1| * p.2 0 ^ 2 :=
      funext fun p => timeDeriv_sampleC12 p.1 p.2
    rw [h]
    exact (continuous_const.mul continuous_fst.abs).mul
      (((continuous_apply (0 : Fin 1)).comp continuous_snd).pow 2)
  contDiff_section := by
    intro s
    have h : sampleC12 s = fun x : Fin 1 → ℝ => s * |s| * x 0 ^ 2 := rfl
    rw [h]
    exact contDiff_const.mul ((contDiff_apply ℝ ℝ (0 : Fin 1)).pow 2)
  continuous_gradient := by
    intro i
    have h : (fun p : ℝ × (Fin 1 → ℝ) => gradient sampleC12 p.1 p.2 i)
        = fun p : ℝ × (Fin 1 → ℝ) => 2 * (p.1 * |p.1|) * p.2 0 :=
      funext fun p => gradient_sampleC12 p.1 p.2 i
    rw [h]
    exact (continuous_const.mul (continuous_fst.mul continuous_fst.abs)).mul
      ((continuous_apply (0 : Fin 1)).comp continuous_snd)
  continuous_hessian := by
    intro i j
    have h : (fun p : ℝ × (Fin 1 → ℝ) => hessian sampleC12 p.1 p.2 i j)
        = fun p : ℝ × (Fin 1 → ℝ) => 2 * (p.1 * |p.1|) :=
      funext fun p => hessian_sampleC12 p.1 p.2 i j
    rw [h]
    exact continuous_const.mul (continuous_fst.mul continuous_fst.abs)
/-- The function `(t, x) ↦ t |t| x₀²` is not `C²` jointly in time and state. -/
theorem not_contDiff_uncurry_sampleC12 : ¬ ContDiff ℝ 2 (Function.uncurry sampleC12) := by
  intro hu
  have h1 : ContDiff ℝ 2 (fun t : ℝ => t * |t|) := by
    have h : ContDiff ℝ 2 fun t : ℝ => Function.uncurry sampleC12 (t, fun _ : Fin 1 => (1 : ℝ)) :=
      hu.comp (contDiff_id.prodMk contDiff_const)
    simpa [Function.uncurry, sampleC12] using h
  have h2 : Differentiable ℝ (deriv fun t : ℝ => t * |t|) := h1.differentiable_deriv_two
  have h3 : (deriv fun t : ℝ => t * |t|) = fun t : ℝ => 2 * |t| :=
    funext fun t => (hasDerivAt_mul_abs t).deriv
  rw [h3] at h2
  have h4 := (h2 0).const_mul (2⁻¹ : ℝ)
  have h5 : (fun t : ℝ => (2⁻¹ : ℝ) * (2 * |t|)) = fun t : ℝ => |t| := by
    funext t; ring
  rw [h5] at h4
  exact not_differentiableAt_abs_zero h4
end Sample

end LevyStochCalc.Ito.JumpFormula


