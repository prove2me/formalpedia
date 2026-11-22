-- Prove2me | Definitions.Def_LevyStochCalc_Ito_C12Product_F000
-- name    : LevyStochCalc_Ito_C12Product_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:01:35.829571+00:00
-- url     : https://prove2.me/theorems/3754b7d3-b3e2-4bce-b274-2506a2acb8af
-- title:
--   Source declarations: LevyStochCalc.Ito.C12Product
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.C12Product. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_C12Mollify_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffIntegrands_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products and linear combinations of `C^{1,2}` functions

The class `C^{1,2}` of functions of time and state is closed under sums, real multiples and
products, and the derivatives of a product obey the Leibniz rules: the first-order rules
`∂_t (u v) = (∂_t u) v + u ∂_t v` in time and `∂_i (u v) = (∂_i u) v + u ∂_i v` in the state,
and the second-order rule
`∂_j ∂_i (u v) = (∂_j ∂_i u) v + (∂_i u) (∂_j v) + (∂_j u) (∂_i v) + u ∂_j ∂_i v`
in the state variable. A function of the pair of time and state that is jointly `C²` is of
class `C^{1,2}` in its curried form, so multiplying a `C^{1,2}` function by such a function —
the time–space cutoff `cutoffFun₂` of the Itô–Lévy formula among them — preserves the class.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.timeDeriv_mul`,
  `LevyStochCalc.Ito.JumpFormula.gradient_mul`,
  `LevyStochCalc.Ito.JumpFormula.hessian_mul` — the Leibniz rules for the time derivative, the
  gradient and the Hessian of a product of two `C^{1,2}` functions.
* `LevyStochCalc.Ito.JumpFormula.IsC12.mul` — a product of `C^{1,2}` functions is `C^{1,2}`.
* `LevyStochCalc.Ito.JumpFormula.isC12_curry_of_contDiff` — a jointly `C²` function of the pair
  of time and state is `C^{1,2}` in its curried form.
* `LevyStochCalc.Ito.JumpFormula.timeDeriv_mul_contDiff`,
  `LevyStochCalc.Ito.JumpFormula.gradient_mul_contDiff`,
  `LevyStochCalc.Ito.JumpFormula.hessian_mul_contDiff`,
  `LevyStochCalc.Ito.JumpFormula.IsC12.mul_contDiff` — the Leibniz rules and the closure
  property for the product of a `C^{1,2}` function with a jointly `C²` function of the pair.
* `LevyStochCalc.Ito.JumpFormula.timeDeriv_add`,
  `LevyStochCalc.Ito.JumpFormula.gradient_add`,
  `LevyStochCalc.Ito.JumpFormula.hessian_add`,
  `LevyStochCalc.Ito.JumpFormula.timeDeriv_const_mul`,
  `LevyStochCalc.Ito.JumpFormula.gradient_const_mul`,
  `LevyStochCalc.Ito.JumpFormula.hessian_const_mul` — the derivatives of a sum and of a real
  multiple.
* `LevyStochCalc.Ito.JumpFormula.IsC12.add`, `LevyStochCalc.Ito.JumpFormula.IsC12.const_mul`,
  `LevyStochCalc.Ito.JumpFormula.IsC12.neg`, `LevyStochCalc.Ito.JumpFormula.IsC12.sub` — the
  class is closed under sums, real multiples, negation and differences.
* `LevyStochCalc.Ito.JumpFormula.isC12_cutoffFun₂` — the time–space cutoff of a `C^{1,2}`
  function is of class `C^{1,2}`.
-/

namespace LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u v : ℝ → (Fin n → ℝ) → ℝ}

section Product

/-- The time derivative of a product of `C^{1,2}` functions. -/
theorem timeDeriv_mul (hu : IsC12 u) (hv : IsC12 v) (t : ℝ) (x : Fin n → ℝ) :
    timeDeriv (fun s y => u s y * v s y) t x
      = timeDeriv u t x * v t x + u t x * timeDeriv v t x :=
  ((hu.hasTimeDeriv t x).fun_mul (hv.hasTimeDeriv t x)).deriv
/-- The gradient of a product of `C^{1,2}` functions. -/
theorem gradient_mul (hu : IsC12 u) (hv : IsC12 v) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    gradient (fun s y => u s y * v s y) t x i
      = gradient u t x i * v t x + u t x * gradient v t x i := by
  have h := ((hu.contDiff_section t).differentiable (by norm_num) x).hasFDerivAt.fun_mul
    ((hv.contDiff_section t).differentiable (by norm_num) x).hasFDerivAt
  simp only [gradient, h.fderiv, add_apply, smul_apply, smul_eq_mul]
  ring
/-- The Hessian of a product of `C^{1,2}` functions. -/
theorem hessian_mul (hu : IsC12 u) (hv : IsC12 v) (t : ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    hessian (fun s y => u s y * v s y) t x i j
      = hessian u t x i j * v t x + gradient u t x i * gradient v t x j
        + gradient u t x j * gradient v t x i + u t x * hessian v t x i j := by
  have hfun : (fun y : Fin n → ℝ => fderiv ℝ (fun z => u t z * v t z) y (Pi.single i 1))
      = fun y : Fin n → ℝ => gradient u t y i * v t y + u t y * gradient v t y i :=
    funext fun y => gradient_mul hu hv t y i
  have h := ((differentiable_gradient_state hu t i x).hasFDerivAt.fun_mul
      ((hv.contDiff_section t).differentiable (by norm_num) x).hasFDerivAt).fun_add
    (((hu.contDiff_section t).differentiable (by norm_num) x).hasFDerivAt.fun_mul
      (differentiable_gradient_state hv t i x).hasFDerivAt)
  have hx : hessian (fun s y => u s y * v s y) t x i j
      = fderiv ℝ (fun y : Fin n → ℝ => gradient u t y i * v t y + u t y * gradient v t y i) x
        (Pi.single j 1) := by
    simp only [hessian, hfun]
  rw [hx, h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [gradient, hessian]
  ring
/-- A product of `C^{1,2}` functions is of class `C^{1,2}`. -/
theorem IsC12.mul (hu : IsC12 u) (hv : IsC12 v) : IsC12 fun s y => u s y * v s y where
  continuous := hu.continuous.mul hv.continuous
  hasTimeDeriv := fun s x => by
    rw [timeDeriv_mul hu hv]
    exact (hu.hasTimeDeriv s x).fun_mul (hv.hasTimeDeriv s x)
  continuous_timeDeriv := by
    have h : (fun p : ℝ × (Fin n → ℝ) => timeDeriv (fun s y => u s y * v s y) p.1 p.2)
        = fun p : ℝ × (Fin n → ℝ) =>
          timeDeriv u p.1 p.2 * v p.1 p.2 + u p.1 p.2 * timeDeriv v p.1 p.2 :=
      funext fun p => timeDeriv_mul hu hv p.1 p.2
    rw [h]
    exact (hu.continuous_timeDeriv.mul hv.continuous).add
      (hu.continuous.mul hv.continuous_timeDeriv)
  contDiff_section := fun s => (hu.contDiff_section s).mul (hv.contDiff_section s)
  continuous_gradient := fun i => by
    have h : (fun p : ℝ × (Fin n → ℝ) => gradient (fun s y => u s y * v s y) p.1 p.2 i)
        = fun p : ℝ × (Fin n → ℝ) =>
          gradient u p.1 p.2 i * v p.1 p.2 + u p.1 p.2 * gradient v p.1 p.2 i :=
      funext fun p => gradient_mul hu hv p.1 p.2 i
    rw [h]
    exact ((hu.continuous_gradient i).mul hv.continuous).add
      (hu.continuous.mul (hv.continuous_gradient i))
  continuous_hessian := fun i j => by
    have h : (fun p : ℝ × (Fin n → ℝ) => hessian (fun s y => u s y * v s y) p.1 p.2 i j)
        = fun p : ℝ × (Fin n → ℝ) =>
          hessian u p.1 p.2 i j * v p.1 p.2 + gradient u p.1 p.2 i * gradient v p.1 p.2 j
            + gradient u p.1 p.2 j * gradient v p.1 p.2 i + u p.1 p.2 * hessian v p.1 p.2 i j :=
      funext fun p => hessian_mul hu hv p.1 p.2 i j
    rw [h]
    exact ((((hu.continuous_hessian i j).mul hv.continuous).add
      ((hu.continuous_gradient i).mul (hv.continuous_gradient j))).add
      ((hu.continuous_gradient j).mul (hv.continuous_gradient i))).add
      (hu.continuous.mul (hv.continuous_hessian i j))
end Product

section ContDiffFactor

variable {g : ℝ × (Fin n → ℝ) → ℝ}

/-- A jointly `C²` function of the pair of time and state is of class `C^{1,2}` in its curried
form. -/
theorem isC12_curry_of_contDiff (hg : ContDiff ℝ 2 g) : IsC12 fun s x => g (s, x) :=
  IsC12.of_contDiff (u := fun s x => g (s, x)) hg
/-- The time derivative of the product of a `C^{1,2}` function with a jointly `C²` function of
the pair of time and state. -/
theorem timeDeriv_mul_contDiff (hu : IsC12 u) (hg : ContDiff ℝ 2 g) (t : ℝ) (x : Fin n → ℝ) :
    timeDeriv (fun s x => u s x * g (s, x)) t x
      = timeDeriv u t x * g (t, x) + u t x * deriv (fun s => g (s, x)) t :=
  timeDeriv_mul hu (isC12_curry_of_contDiff hg) t x
/-- The gradient of the product of a `C^{1,2}` function with a jointly `C²` function of the
pair of time and state. -/
theorem gradient_mul_contDiff (hu : IsC12 u) (hg : ContDiff ℝ 2 g) (t : ℝ) (x : Fin n → ℝ)
    (i : Fin n) :
    gradient (fun s x => u s x * g (s, x)) t x i
      = gradient u t x i * g (t, x) + u t x * fderiv ℝ (fun y => g (t, y)) x (Pi.single i 1) :=
  gradient_mul hu (isC12_curry_of_contDiff hg) t x i
/-- The Hessian of the product of a `C^{1,2}` function with a jointly `C²` function of the pair
of time and state. -/
theorem hessian_mul_contDiff (hu : IsC12 u) (hg : ContDiff ℝ 2 g) (t : ℝ) (x : Fin n → ℝ)
    (i j : Fin n) :
    hessian (fun s x => u s x * g (s, x)) t x i j
      = hessian u t x i j * g (t, x)
        + gradient u t x i * fderiv ℝ (fun y => g (t, y)) x (Pi.single j 1)
        + gradient u t x j * fderiv ℝ (fun y => g (t, y)) x (Pi.single i 1)
        + u t x
          * fderiv ℝ (fun y => fderiv ℝ (fun z => g (t, z)) y (Pi.single i 1)) x
              (Pi.single j 1) :=
  hessian_mul hu (isC12_curry_of_contDiff hg) t x i j
/-- The product of a `C^{1,2}` function with a jointly `C²` function of the pair of time and
state is of class `C^{1,2}`. -/
theorem IsC12.mul_contDiff (hu : IsC12 u) (hg : ContDiff ℝ 2 g) :
    IsC12 fun s x => u s x * g (s, x) :=
  hu.mul (isC12_curry_of_contDiff hg)
end ContDiffFactor

section Linear

/-- The time derivative of a sum of `C^{1,2}` functions. -/
theorem timeDeriv_add (hu : IsC12 u) (hv : IsC12 v) (t : ℝ) (x : Fin n → ℝ) :
    timeDeriv (fun s y => u s y + v s y) t x = timeDeriv u t x + timeDeriv v t x :=
  ((hu.hasTimeDeriv t x).fun_add (hv.hasTimeDeriv t x)).deriv
/-- The gradient of a sum of `C^{1,2}` functions. -/
theorem gradient_add (hu : IsC12 u) (hv : IsC12 v) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    gradient (fun s y => u s y + v s y) t x i = gradient u t x i + gradient v t x i := by
  have h := ((hu.contDiff_section t).differentiable (by norm_num) x).hasFDerivAt.fun_add
    ((hv.contDiff_section t).differentiable (by norm_num) x).hasFDerivAt
  simp only [gradient, h.fderiv, add_apply]
/-- The Hessian of a sum of `C^{1,2}` functions. -/
theorem hessian_add (hu : IsC12 u) (hv : IsC12 v) (t : ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    hessian (fun s y => u s y + v s y) t x i j = hessian u t x i j + hessian v t x i j := by
  have hfun : (fun y : Fin n → ℝ => fderiv ℝ (fun z => u t z + v t z) y (Pi.single i 1))
      = fun y : Fin n → ℝ => gradient u t y i + gradient v t y i :=
    funext fun y => gradient_add hu hv t y i
  have h := (differentiable_gradient_state hu t i x).hasFDerivAt.fun_add
    (differentiable_gradient_state hv t i x).hasFDerivAt
  have hx : hessian (fun s y => u s y + v s y) t x i j
      = fderiv ℝ (fun y : Fin n → ℝ => gradient u t y i + gradient v t y i) x
        (Pi.single j 1) := by
    simp only [hessian, hfun]
  rw [hx, h.fderiv, add_apply]
  rfl
/-- A sum of `C^{1,2}` functions is of class `C^{1,2}`. -/
theorem IsC12.add (hu : IsC12 u) (hv : IsC12 v) : IsC12 fun s y => u s y + v s y where
  continuous := hu.continuous.add hv.continuous
  hasTimeDeriv := fun s x => by
    rw [timeDeriv_add hu hv]
    exact (hu.hasTimeDeriv s x).fun_add (hv.hasTimeDeriv s x)
  continuous_timeDeriv := by
    have h : (fun p : ℝ × (Fin n → ℝ) => timeDeriv (fun s y => u s y + v s y) p.1 p.2)
        = fun p : ℝ × (Fin n → ℝ) => timeDeriv u p.1 p.2 + timeDeriv v p.1 p.2 :=
      funext fun p => timeDeriv_add hu hv p.1 p.2
    rw [h]
    exact hu.continuous_timeDeriv.add hv.continuous_timeDeriv
  contDiff_section := fun s => (hu.contDiff_section s).add (hv.contDiff_section s)
  continuous_gradient := fun i => by
    have h : (fun p : ℝ × (Fin n → ℝ) => gradient (fun s y => u s y + v s y) p.1 p.2 i)
        = fun p : ℝ × (Fin n → ℝ) => gradient u p.1 p.2 i + gradient v p.1 p.2 i :=
      funext fun p => gradient_add hu hv p.1 p.2 i
    rw [h]
    exact (hu.continuous_gradient i).add (hv.continuous_gradient i)
  continuous_hessian := fun i j => by
    have h : (fun p : ℝ × (Fin n → ℝ) => hessian (fun s y => u s y + v s y) p.1 p.2 i j)
        = fun p : ℝ × (Fin n → ℝ) => hessian u p.1 p.2 i j + hessian v p.1 p.2 i j :=
      funext fun p => hessian_add hu hv p.1 p.2 i j
    rw [h]
    exact (hu.continuous_hessian i j).add (hv.continuous_hessian i j)
/-- The time derivative of a real multiple of a `C^{1,2}` function. -/
theorem timeDeriv_const_mul (hu : IsC12 u) (c : ℝ) (t : ℝ) (x : Fin n → ℝ) :
    timeDeriv (fun s y => c * u s y) t x = c * timeDeriv u t x :=
  ((hu.hasTimeDeriv t x).const_mul c).deriv
/-- The gradient of a real multiple of a `C^{1,2}` function. -/
theorem gradient_const_mul (hu : IsC12 u) (c : ℝ) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    gradient (fun s y => c * u s y) t x i = c * gradient u t x i := by
  have h := ((hu.contDiff_section t).differentiable (by norm_num) x).hasFDerivAt.const_mul c
  simp only [gradient, h.fderiv, smul_apply, smul_eq_mul]
/-- The Hessian of a real multiple of a `C^{1,2}` function. -/
theorem hessian_const_mul (hu : IsC12 u) (c : ℝ) (t : ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    hessian (fun s y => c * u s y) t x i j = c * hessian u t x i j := by
  have hfun : (fun y : Fin n → ℝ => fderiv ℝ (fun z => c * u t z) y (Pi.single i 1))
      = fun y : Fin n → ℝ => c * gradient u t y i :=
    funext fun y => gradient_const_mul hu c t y i
  have h := (differentiable_gradient_state hu t i x).hasFDerivAt.const_mul c
  have hx : hessian (fun s y => c * u s y) t x i j
      = fderiv ℝ (fun y : Fin n → ℝ => c * gradient u t y i) x (Pi.single j 1) := by
    simp only [hessian, hfun]
  rw [hx, h.fderiv, smul_apply, smul_eq_mul]
  rfl
/-- A real multiple of a `C^{1,2}` function is of class `C^{1,2}`. -/
theorem IsC12.const_mul (hu : IsC12 u) (c : ℝ) : IsC12 fun s y => c * u s y :=
  (isC12_curry_of_contDiff (g := fun _ : ℝ × (Fin n → ℝ) => c) contDiff_const).mul hu
/-- The negative of a `C^{1,2}` function is of class `C^{1,2}`. -/
theorem IsC12.neg (hu : IsC12 u) : IsC12 fun s y => -u s y := by
  have h := hu.const_mul (-1)
  have hx : (fun s (y : Fin n → ℝ) => -u s y) = fun s (y : Fin n → ℝ) => (-1 : ℝ) * u s y := by
    funext s y
    ring
  rw [hx]
  exact h
/-- A difference of `C^{1,2}` functions is of class `C^{1,2}`. -/
theorem IsC12.sub (hu : IsC12 u) (hv : IsC12 v) : IsC12 fun s y => u s y - v s y := by
  have h := hu.add hv.neg
  have hx : (fun s (y : Fin n → ℝ) => u s y - v s y)
      = fun s (y : Fin n → ℝ) => u s y + -v s y := by
    funext s y
    ring
  rw [hx]
  exact h
end Linear

/-- The product of a `C^{1,2}` function with the time–space cutoff of radius `R` is of class
`C^{1,2}`. -/
theorem isC12_cutoffFun₂ (hu : IsC12 u) (R : ℝ) :
    IsC12 (JumpFormulaCutoff.cutoffFun₂ u R) :=
  hu.mul_contDiff (g := JumpFormulaCutoff.timeBoxCut R) (JumpFormulaCutoff.contDiff_timeBoxCut R)
end LevyStochCalc.Ito.JumpFormula


