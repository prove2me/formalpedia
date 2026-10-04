-- Prove2me | Definitions.Def_ChapterQuadraticRotationEsa
-- name    : ChapterQuadraticRotationEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T19:02:24.585988+00:00
-- url     : https://prove2.me/theorems/a80ba498-6de4-471c-85fd-8963cd71e23e
-- title:
--   The Lean 4 theorem `rot_dot` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQuadraticRotationEsa.lean`): generated def bundle for ChapterQuadraticRotationEsa. See BookProof/ChapterQuadraticRotationEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib


/-!
# General (non-diagonal) quadratic Hamiltonians of arbitrary signature

`BookProof.ChapterHyperbolicQuadraticEsa` proves that the *diagonal* quadratic operator

`H_c = ∑ᵢ cᵢ (−∂ᵢ² + xᵢ²/4)`,  `c : Fin d → ℝ` arbitrary (hyperbolic signatures included),

is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`.
This module removes the diagonality restriction: for an **arbitrary real symmetric matrix**
`A` the operator

`H_A = ∑_{k,l} A_{kl} (π_k π_l + x_k x_l / 4)`,  `π_k = −i ∂/∂x_k`,

— the general quadratic Hamiltonian whose kinetic and potential forms share the matrix
`A`, of arbitrary signature — is symmetric and essentially self-adjoint on the same core.
With `A = diag(c)` this is the diagonal theorem; with `A` a rotated Minkowski form it is
`□ + V` written in rotated coordinates, where neither the kinetic form nor the potential
is diagonal.

## The route

An orthogonal change of coordinates.  The Gaussian `e^{−‖x‖²/4}` is rotation invariant, so
composition with an orthogonal matrix `O` maps the Gauss–polynomial core onto itself; on
the polynomial coordinates it is the substitution `rotPoly O`, an algebra automorphism.
The canonical pair transforms contravariantly with the *same* matrix
(`rotPoly_mulXPoly`, `rotPoly_momPoly`), so the diagonal operator `H_c` is carried onto
`H_A` with `A = O diag(c) Oᵀ` (`quadPolyMat_rotPoly`).  The rotated product Hermite
functions are therefore an orthonormal family of joint eigenvectors of `H_A` spanning the
core (`orthonormal_rotHermiteLp`, `span_rotHermiteLp`, `quadOpMat_rotHermiteLp`), and the
diagonal instruments of `BookProof.ChapterHyperbolicQuadraticEsa`
(`symmetricOn_of_diagonal`, `deficiencyTrivialAt_of_diagonal`) finish the argument.
The spectral theorem for real symmetric matrices supplies `O` and `c` for an arbitrary
symmetric `A`.

## What is proved

* `rotPoly`, `pderiv_rotPoly`, `rotPoly_mulXPoly`, `rotPoly_momPoly` — the orthogonal
  substitution on polynomial coordinates and its action on the canonical pair;
* `rotIso`, `gaussInt_rotPoly`, `inner_pgLp_rotPoly` — the rotation as a
  measure-preserving linear isometry of `ℝᵈ`, and the resulting unitarity on the core;
* `quadPolyMat`, `quadPolyMat_rotPoly` — the general quadratic operator and the
  conjugation identity `H_{O diag(c) Oᵀ} ∘ R = R ∘ H_c`;
* `rotHermiteLp`, `orthonormal_rotHermiteLp`, `span_rotHermiteLp` — the rotated product
  Hermite functions are an orthonormal family whose span is the core;
* `quadOpMat_rotConj_symmetric`, `quadOpMat_rotConj_essentiallySelfAdjoint` — the headline
  for `A = O diag(c) Oᵀ`;
* `quadOpMat_symmetric`, `quadOpMat_essentiallySelfAdjoint` — **the headline**: for every
  real symmetric matrix `A`, `H_A` is symmetric and essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝᵈ)`;
* `quadOpMat_not_bounded`, `polyGaussCore_dense_L2` — non-vacuity: the operator is
  genuinely unbounded whenever `A ≠ 0`, and its domain is dense.

## Honest boundary

The potential is quadratic and its matrix is *the same* as the matrix of the kinetic form:
that matched pair is what a single rotation diagonalizes.  A general Faris–Lavine
potential bounded above by a quadratic remains out of reach by this argument, exactly as
recorded in `BookProof.ChapterHyperbolicQuadraticEsa`.
-/

namespace BookProof.QuadraticRotation

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

/-! ## 1. The orthogonal substitution on polynomial coordinates -/

/-- The substitution `Xᵢ ↦ ∑ⱼ Oⱼᵢ Xⱼ`: on functions this is `p ↦ p ∘ Oᵀ`. -/
def rotPoly (O : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ :=
  aeval (fun i => ∑ j, C ((O j i : ℝ) : ℂ) * X j)











/-! ## 2. The canonical pair transforms with the same matrix -/







/-! ## 3. The general quadratic operator and the conjugation identity -/

/-- The general quadratic Hamiltonian `∑_{k,l} A_{kl}(π_k π_l + x_k x_l/4)` in polynomial
coordinates. -/
def quadPolyMat (A : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ k, ∑ l, ((A k l : ℝ) : ℂ) •
    ((momPoly k).comp (momPoly l) + (1/4 : ℂ) • ((mulXPoly k).comp (mulXPoly l)))







/-- `O diag(c) Oᵀ`, written entrywise. -/
def rotConj (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => ∑ i, O k i * c i * O l i





/-! ## 4. The rotation as a measure-preserving isometry of `ℝᵈ` -/

/-- The linear map `x ↦ Oᵀx` of `ℝᵈ`. -/
def rotLin (O : Matrix (Fin d) (Fin d) ℝ) : Vd d →ₗ[ℝ] Vd d where
  toFun x := (WithLp.toLp 2 (fun i => ∑ j, O j i * x j))
  map_add' x y := by ext i; simp [Finset.sum_add_distrib, mul_add]
  map_smul' t x := by
    ext i
    change ∑ j, O j i * (t * x j) = t * ∑ j, O j i * x j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

@[simp] theorem rotLin_apply (O : Matrix (Fin d) (Fin d) ℝ) (x : Vd d) (i : Fin d) :
    rotLin O x i = ∑ j, O j i * x j := rfl

theorem rot_dot {O : Matrix (Fin d) (Fin d) ℝ} (hOO : O * Oᵀ = 1) (a b : Fin d → ℝ) :
    ∑ k, (∑ j, O j k * a j) * (∑ l, O l k * b l) = ∑ j, a j * b j := by
  have hstep : ∀ k : Fin d, (∑ j, O j k * a j) * (∑ l, O l k * b l)
      = ∑ j, ∑ l, (O j k * O l k) * (a j * b l) := by
    intro k
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_comm]
  have hj : ∀ j : Fin d, ∑ k, ∑ l, (O j k * O l k) * (a j * b l) = a j * b j := by
    intro j
    rw [Finset.sum_comm]
    have h2 : ∀ l : Fin d, ∑ k, (O j k * O l k) * (a j * b l)
        = (if j = l then (1 : ℝ) else 0) * (a j * b l) := by
      intro l
      rw [← Finset.sum_mul]
      congr 1
      simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hOO j) l
    rw [Finset.sum_congr rfl fun l _ => h2 l]
    simp
  rw [Finset.sum_congr rfl fun j _ => hj j]

theorem rotLin_inner {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (x y : Vd d) :
    inner ℝ (rotLin O x) (rotLin O y) = inner ℝ x y := by
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, rotLin_apply]
  simpa [mul_comm] using rot_dot hOO (fun j => y j) (fun j => x j)

/-- The orthogonal matrix as a linear isometry equivalence of `ℝᵈ`. -/
def rotIso {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) : Vd d ≃ₗᵢ[ℝ] Vd d :=
  ((rotLin O).isometryOfInner (rotLin_inner hO)).toLinearIsometryEquiv rfl

@[simp] theorem rotIso_apply {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (x : Vd d) :
    (rotIso hO x : Vd d) = rotLin O x := rfl











/-! ## 5. The rotated product Hermite basis -/

/-- The rotated product Hermite functions `ψ_α ∘ Oᵀ`. -/
def rotHermiteLp (O : Matrix (Fin d) (Fin d) ℝ) (a : Fin d →₀ ℕ) : L2d d :=
  ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (rotPoly O (hermiteMv a))













/-! ## 6. The Hamiltonian on the core, and essential self-adjointness -/

/-- **The general quadratic Hamiltonian on the Gauss–polynomial core of `L²(ℝᵈ)`.** -/
def quadOpMat (A : Matrix (Fin d) (Fin d) ℝ) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (quadPolyMat A)





















/-! ## 7. Non-vacuity -/







end

end BookProof.QuadraticRotation


