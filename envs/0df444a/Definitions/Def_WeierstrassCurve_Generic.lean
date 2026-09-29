-- Prove2me | Definitions.Def_WeierstrassCurve_Generic
-- name    : WeierstrassCurve_Generic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/e0bb9c5b-0ea6-5b87-ac1a-ed53f69b2ad3
-- title:
--   The generic Weierstrass equation and the generic elliptic curve
-- statement:
--   For a commutative ring $K$, [`WeierstrassCurve.Generic.poly K`](../def/WeierstrassCurve_Generic.html#L17) is the Weierstrass equation over the polynomial ring `MvPolynomial (Fin 5) K` $= K[A_1,A_2,A_3,A_4,A_6]$ whose five coefficients $a_1,a_2,a_3,a_4,a_6$ are the five indeterminates $X_0,\dots,X_4$, i.e. $y^2 + A_1xy + A_3y = x^3 + A_2x^2 + A_4x + A_6$; the `poly_a…` lemmas record each coefficient. Dually, `coeffs W` packages the coefficients of a Weierstrass equation $W$ over any type as a function $\mathrm{Fin}\,5 \to A$ (with the five evident projection lemmas). For a commutative $K$-algebra $A$ and $W : \mathrm{WeierstrassCurve}\,A$, the classifying map `classify K W` is the $K$-algebra homomorphism $K[A_1,\dots,A_6] \to A$ given by evaluation at `coeffs W`, so $X_i \mapsto$ the $i$-th coefficient of $W$; `poly_map_classify` says that base-changing `poly K` along it returns $W$, and `eq_classify_of_poly_map_eq` says it is the unique $K$-algebra map doing so. Thus $K[A_1,\dots,A_6]$ represents the functor of Weierstrass equations on $K$-algebras. `Δ_poly_map` is the compatibility of the discriminant with base change along a ring map, and `Δ_poly_ne_zero` asserts that the discriminant of `poly K` is a nonzero polynomial whenever $K$ is nontrivial, obtained by specialising to $y^2+y=x^3-x$ and $y^2+y=x^3$.
--
--   For a field $K$, `FunctionField K` abbreviates the fraction field of $K[A_1,\dots,A_6]$ and `Closure K` an algebraic closure $\Omega$ of it; both are in the same universe as $K$. The generic elliptic curve `curve K` is the base change of `poly K` to $\Omega$, its coefficients being the images of the indeterminates. The structure maps $K[A_1,\dots,A_6] \to$ `FunctionField K` $\to \Omega$ are injective, whence $\Delta(\mathrm{curve}\,K) \neq 0$, hence a unit in the field $\Omega$, so `curve K` is registered as elliptic. Finally `curve_map_algEquiv` states that `curve K` is carried to itself by every $K(A_1,\dots,A_6)$-algebra automorphism of $\Omega$.
--
--   **Relation to Mathlib.** Built on Mathlib's `WeierstrassCurve`, its base change `WeierstrassCurve.map`, the discriminant `Δ` and the `IsElliptic` class; Mathlib has no universal/generic Weierstrass equation, and the representability statement (`classify`, `poly_map_classify`, `eq_classify_of_poly_map_eq`) is the project's own.
--
--   **Where it is used.** The generic curve over $\Omega$ serves as the geometric generic fibre of the universal Weierstrass family, a setting in which statements about $p$-torsion level structures (monodromy, irreducibility of the associated modular curves) can be formulated for a single curve; it is imported by several modules of the tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_Generic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

noncomputable section

open MvPolynomial

namespace WeierstrassCurve.Generic

section CommRing

variable (K : Type u) [CommRing K]

def poly : WeierstrassCurve (MvPolynomial (Fin 5) K) :=
  ⟨X 0, X 1, X 2, X 3, X 4⟩

@[simp] theorem poly_a₁ : (poly K).a₁ = X 0 := rfl
@[simp] theorem poly_a₂ : (poly K).a₂ = X 1 := rfl
@[simp] theorem poly_a₃ : (poly K).a₃ = X 2 := rfl
@[simp] theorem poly_a₄ : (poly K).a₄ = X 3 := rfl
@[simp] theorem poly_a₆ : (poly K).a₆ = X 4 := rfl

variable {K}

section coeffs

variable {A : Type v}

def coeffs (W : WeierstrassCurve A) : Fin 5 → A := ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

@[simp] theorem coeffs_zero (W : WeierstrassCurve A) : coeffs W 0 = W.a₁ := rfl
@[simp] theorem coeffs_one (W : WeierstrassCurve A) : coeffs W 1 = W.a₂ := rfl
@[simp] theorem coeffs_two (W : WeierstrassCurve A) : coeffs W 2 = W.a₃ := rfl
@[simp] theorem coeffs_three (W : WeierstrassCurve A) : coeffs W 3 = W.a₄ := rfl
@[simp] theorem coeffs_four (W : WeierstrassCurve A) : coeffs W 4 = W.a₆ := rfl

end coeffs

theorem Δ_poly_map {A : Type v} [CommRing A] (f : MvPolynomial (Fin 5) K →+* A) :
    ((poly K).map f).Δ = f (poly K).Δ :=
  (poly K).map_Δ f

variable {A : Type v} [CommRing A] [Algebra K A]

variable (K) in

def classify (W : WeierstrassCurve A) : MvPolynomial (Fin 5) K →ₐ[K] A :=
  MvPolynomial.aeval (coeffs W)

@[simp] theorem classify_X (W : WeierstrassCurve A) (i : Fin 5) :
    classify K W (X i) = coeffs W i := by
  simp [classify]

@[simp] theorem poly_map_classify (W : WeierstrassCurve A) :
    (poly K).map (classify K W : MvPolynomial (Fin 5) K →+* A) = W := by
  rcases W with ⟨a₁, a₂, a₃, a₄, a₆⟩
  simp [poly, WeierstrassCurve.map, coeffs]

theorem eq_classify_of_poly_map_eq (W : WeierstrassCurve A) (f : MvPolynomial (Fin 5) K →ₐ[K] A)
    (hf : (poly K).map (f : MvPolynomial (Fin 5) K →+* A) = W) : f = classify K W := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [classify_X]
  subst hf
  fin_cases i <;> rfl

variable (K) in

theorem Δ_poly_ne_zero [Nontrivial K] : (poly K).Δ ≠ 0 := by
  intro h

  have h₁ : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve K).Δ = 0 := by
    rw [← poly_map_classify (K := K) (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve K), Δ_poly_map, h,
      map_zero]
  have h₂ : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).Δ = 0 := by
    rw [← poly_map_classify (K := K) (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K), Δ_poly_map, h,
      map_zero]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at h₁ h₂
  have e : (1 : K) = 0 := by linear_combination (-11) * h₂ - 8 * h₁
  exact one_ne_zero e

end CommRing

section Field

variable (K : Type u) [Field K]

abbrev FunctionField : Type u := FractionRing (MvPolynomial (Fin 5) K)

abbrev Closure : Type u := AlgebraicClosure (FunctionField K)

def curve : WeierstrassCurve (Closure K) :=
  (poly K).map (algebraMap (MvPolynomial (Fin 5) K) (Closure K))

theorem curve_def : curve K = (poly K).map (algebraMap (MvPolynomial (Fin 5) K) (Closure K)) := rfl

theorem algebraMap_functionField_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 5) K) (FunctionField K)) :=
  IsFractionRing.injective _ _

theorem algebraMap_closure_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 5) K) (Closure K)) := by
  rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 5) K) (FunctionField K) (Closure K)]
  exact (algebraMap (FunctionField K) (Closure K)).injective.comp
    (algebraMap_functionField_injective K)

theorem Δ_curve : (curve K).Δ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (poly K).Δ :=
  (poly K).map_Δ _

theorem Δ_curve_ne_zero : (curve K).Δ ≠ 0 := by
  rw [Δ_curve]
  exact (map_ne_zero_iff _ (algebraMap_closure_injective K)).2 (Δ_poly_ne_zero K)

theorem isUnit_Δ_curve : IsUnit (curve K).Δ :=
  (Δ_curve_ne_zero K).isUnit

instance isElliptic_curve : (curve K).IsElliptic := ⟨isUnit_Δ_curve K⟩

@[simp] theorem curve_a₁ : (curve K).a₁ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 0) := rfl
@[simp] theorem curve_a₂ : (curve K).a₂ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 1) := rfl
@[simp] theorem curve_a₃ : (curve K).a₃ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 2) := rfl
@[simp] theorem curve_a₄ : (curve K).a₄ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 3) := rfl
@[simp] theorem curve_a₆ : (curve K).a₆ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 4) := rfl

theorem curve_map_algEquiv (σ : Closure K ≃ₐ[FunctionField K] Closure K) :
    (curve K).map (σ : Closure K →+* Closure K) = curve K := by
  rw [curve_def, WeierstrassCurve.map_map]
  congr 1
  ext x
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 5) K) (FunctionField K) (Closure K)]
    exact σ.commutes _
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 5) K) (FunctionField K) (Closure K)]
    exact σ.commutes _

end Field

end WeierstrassCurve.Generic

end


