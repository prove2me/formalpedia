-- Prove2me | Definitions.Def_ChapterAbelianCyclicModel
-- name    : ChapterAbelianCyclicModel
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-17T00:54:53.21975+00:00
-- url     : https://prove2.me/theorems/87f37a55-ef6d-499e-958b-7641713458d7
-- title:
--   The Lean 4 theorem `repState_star_mul_self` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAbelianCyclicModel.lean`): generated def bundle for ChapterAbelianCyclicModel. See BookProof/ChapterAbelianCyclicModel.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAbelianCyclicModel.lean

import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_integral_stateMeasure

import Definitions.Def_ChapterAbelianGelfandModel
import Mathlib


/-!
# Abelian algebras with a cyclic vector: the multiplication model (plan GAP-2)

`ChapterSpectralMultiplication` proves the multiplication model for a **singly
generated** abelian algebra: a normal operator `T` with a cyclic unit vector is
multiplication by `z` on `L²(μ)`.  The obstruction recorded there — and in
`BookProof/STATUS.md` — was the passage from a singly generated abelian algebra to
an *arbitrary* one, which the classical theory obtains by producing a single
generator.

This module removes the need for a generator.  The whole argument of
`ChapterSpectralMultiplication` is carried out for an **arbitrary unital
`*`-representation** `π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)` of the continuous functions on
a compact Hausdorff space, with a cyclic unit vector `ξ`:

* `repState` — `f ↦ ⟪ξ, π(f) ξ⟫` is a state of `C(X, ℂ)`; positivity is
  `⟪ξ, π(f̄f)ξ⟫ = ‖π(f)ξ‖²`, which uses only that `π` preserves products and stars
  (no continuity of `π` is assumed anywhere in this file);
* `repMeasure` — its Riesz measure, a regular Borel probability measure on `X`, with
  `integral_repMeasure : ⟪ξ, π(f)ξ⟫ = ∫ f dμ`;
* `norm_rep_apply` — the isometry `‖π(f)ξ‖ = ‖f‖_{L²(μ)}`;
* `cyclicRepUnitary` — hence `f ↦ π(f)ξ` extends to a **unitary**
  `U : L²(μ) ≃ₗᵢ[ℂ] H`;
* `cyclicRepUnitary_intertwines` and HEADLINE
  `cyclic_representation_multiplication_model` — `U` conjugates multiplication by
  `g` on `L²(μ)` into `π(g)`, for *every* continuous symbol `g` simultaneously.

Composing with Gelfand duality gives the form the classification programme needs
(`abelian_algebra_multiplication_model`): **every representation of a commutative
unital C\*-algebra `A` on a Hilbert space with a cyclic unit vector is unitarily
equivalent to the representation of `A` by multiplication operators on the `L²`
space of a Borel probability measure on the character space of `A`** — no
generator, no separability, no normality of a distinguished element.

Everything is `sorry`-free and `axiom`-free.
-/

open MeasureTheory Complex WeakDual
open scoped ComplexOrder

namespace BookProof.ChapterAbelianCyclicModel

open BookProof.ChapterAbelianGelfandModel

section Rep

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)

/-! ## 1. The vector state of a representation -/

/-- **The vector state** `f ↦ ⟪ξ, π(f) ξ⟫` of a representation at a vector. -/
noncomputable def repState : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f := inner ℂ xi (pi f xi)
  map_add' f g := by simp
  map_smul' c f := by simp

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem repState_apply (f : C(X, ℂ)) :
    repState pi xi f = inner ℂ xi (pi f xi) := rfl

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
/-- `⟪ξ, π(f̄f)ξ⟫ = ‖π(f)ξ‖²`: the vector state is **positive**. -/
theorem repState_star_mul_self (f : C(X, ℂ)) :
    repState pi xi (star f * f) = ((‖pi f xi‖ : ℝ) ^ 2 : ℂ) := by
  have h1 : pi (star f * f) = star (pi f) * pi f := by rw [map_mul, map_star]
  have h2 : ((star (pi f) * pi f) xi)
      = ContinuousLinearMap.adjoint (pi f) ((pi f) xi) := by
    simp [ContinuousLinearMap.star_eq_adjoint]
  simp only [repState_apply, h1, h2, ContinuousLinearMap.adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem repState_pos (f : C(X, ℂ)) : 0 ≤ repState pi xi (star f * f) := by
  rw [repState_star_mul_self]
  simp [Complex.zero_le_real]



/-! ## 2. The measure of the representation -/

/-- **The measure of the representation at `ξ`**: the Riesz measure of the vector
state, a regular Borel measure on `X`. -/
noncomputable def repMeasure : Measure X :=
  stateMeasure (repState pi xi) (repState_pos pi xi)

instance instIsFiniteMeasureRepMeasure : IsFiniteMeasure (repMeasure pi xi) := by
  unfold repMeasure
  infer_instance

instance instRegularRepMeasure : (repMeasure pi xi).Regular := by
  unfold repMeasure
  infer_instance





/-! ## 3. The isometry `f ↦ π(f)ξ` -/

/-- The linear map `f ↦ π(f)ξ` from continuous functions to `H`. -/
noncomputable def repVec : C(X, ℂ) →ₗ[ℂ] H where
  toFun f := pi f xi
  map_add' f g := by simp
  map_smul' c f := by simp

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem repVec_apply (f : C(X, ℂ)) : repVec pi xi f = pi f xi := rfl

/-- **The key isometry**: `‖π(f)ξ‖` is the `L²(μ)` norm of `f`. -/
theorem norm_rep_apply (f : C(X, ℂ)) :
    ‖pi f xi‖ = ‖ContinuousMap.toLp 2 (repMeasure pi xi) ℂ f‖ := by
  set mu := repMeasure pi xi with hmu
  have hL : ((‖pi f xi‖ : ℝ) ^ 2 : ℂ) = ∫ x, (starRingEnd ℂ) (f x) * f x ∂mu := by
    rw [← repState_star_mul_self pi xi f]
    have h := integral_stateMeasure (repState pi xi) (repState_pos pi xi) (star f * f)
    rw [h]
    rfl
  have hR : ((‖ContinuousMap.toLp 2 mu ℂ f‖ : ℝ) ^ 2 : ℂ)
      = ∫ x, (starRingEnd ℂ) (f x) * f x ∂mu := by
    have h1 : (inner ℂ (ContinuousMap.toLp 2 mu ℂ f) (ContinuousMap.toLp 2 mu ℂ f) : ℂ)
        = ((‖ContinuousMap.toLp 2 mu ℂ f‖ : ℝ) ^ 2 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [← h1, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) mu (𝕜 := ℂ) f] with x hx
    rw [RCLike.inner_apply', hx]
  have hsq : (‖pi f xi‖ : ℝ) ^ 2 = (‖ContinuousMap.toLp 2 mu ℂ f‖ : ℝ) ^ 2 := by
    have hc : ((‖pi f xi‖ : ℝ) ^ 2 : ℂ) = ((‖ContinuousMap.toLp 2 mu ℂ f‖ : ℝ) ^ 2 : ℂ) := by
      rw [hL, hR]
    exact_mod_cast hc
  have h1 : (0 : ℝ) ≤ ‖pi f xi‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖ContinuousMap.toLp 2 mu ℂ f‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

/-! ## 4. The unitary and the multiplication form -/

variable (hcyc : DenseRange (repVec pi xi))

/-- **The unitary of a cyclic representation.**  For a cyclic vector `ξ`, the isometry
`f ↦ π(f)ξ` extends to a unitary from `L²(μ)` onto `H`. -/
noncomputable def cyclicRepUnitary : Lp ℂ 2 (repMeasure pi xi) ≃ₗᵢ[ℂ] H :=
  (LinearEquiv.refl ℂ C(X, ℂ)).extendOfIsometry
    (ContinuousMap.toLp 2 (repMeasure pi xi) ℂ).toLinearMap
    (repVec pi xi)
    (ContinuousMap.toLp_denseRange ℂ _ (μ := repMeasure pi xi) (by simp))
    hcyc
    (fun f => norm_rep_apply pi xi f)

@[simp] theorem cyclicRepUnitary_toLp (f : C(X, ℂ)) :
    cyclicRepUnitary pi xi hcyc (ContinuousMap.toLp 2 (repMeasure pi xi) ℂ f)
      = pi f xi :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f







end Rep

/-! ## 5. The Gelfand form: an arbitrary commutative unital C*-algebra -/

section Gelfand

variable {A : Type*} [CommCStarAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A representation of `A` read as a representation of `C(characterSpace ℂ A, ℂ)`
through the inverse Gelfand transform. -/
noncomputable def gelfandRep (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    C(characterSpace ℂ A, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  rho.comp ((gelfandModel A).symm : C(characterSpace ℂ A, ℂ) →⋆ₐ[ℂ] A)

@[simp] theorem gelfandRep_gelfandModel (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    gelfandRep rho (gelfandModel A a) = rho a := by
  simp [gelfandRep]



end Gelfand

end BookProof.ChapterAbelianCyclicModel


