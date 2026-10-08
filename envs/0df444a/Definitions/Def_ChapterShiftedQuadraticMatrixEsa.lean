-- Prove2me | Definitions.Def_ChapterShiftedQuadraticMatrixEsa
-- name    : ChapterShiftedQuadraticMatrixEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T14:33:31.684614+00:00
-- url     : https://prove2.me/theorems/23dbac9c-b3a2-44e6-b9ed-ead7c50cde30
-- title:
--   Chapter ShiftedQuadraticMatrixEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterShiftedQuadraticMatrixEsa.lean`): generated def bundle for ChapterShiftedQuadraticMatrixEsa. See BookProof/ChapterShiftedQuadraticMatrixEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedQuadraticMatrixEsa.lean

import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Mathlib


/-!
# The indefinite quadratic Hamiltonian **with cross terms** and an unbounded
first-order perturbation

`BookProof.ChapterQuadraticRotationPerturbed` proves that for a **positive definite** real
symmetric matrix `A` and arbitrary real `b, b'` the operator
`H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`, `H_A = ∑_{k,l} A_{kl}(π_kπ_l + x_kx_l/4)`, is essentially
self-adjoint on the Gauss–polynomial core; positive definiteness is used exactly once, to
produce the relative bound, and the indefinite case was the recorded boundary.
`BookProof.ChapterShiftedQuadraticEsa` removes the sign condition for **diagonal** weights,
by completing the square on a translated, modulated core.

This module combines the two: for **every** real symmetric **invertible** `A` — no sign
condition, so the signature may be elliptic, hyperbolic or anything in between — and
arbitrary real `b, b'`, the operator

`H = ∑_{k,l} A_{kl}(π_kπ_l + x_kx_l/4) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`,  `πᵢ = −i∂/∂xᵢ`,

is symmetric and essentially self-adjoint on the translated, modulated Gauss–polynomial
core `D_{a,k}` of `BookProof.ChapterShiftedHermiteCore`, where `a = −2A⁻¹b` and
`k = −A⁻¹b'/2` are the classical equilibrium position and momentum.

The mechanism is again completing the square, now in matrix form:

`∑_{p,q} A_{pq}((π_p + k_p)(π_q + k_q) + (x_p + a_p)(x_q + a_q)/4)
   + ∑ᵢ (bᵢ(xᵢ + aᵢ) + b'ᵢ(πᵢ + kᵢ)) = H_A + const`

as soon as `A a = −2b` and `A k = −b'/2`, and `H_A` is diagonal on the *rotated* Hermite
polynomials, so the *translated, modulated, rotated* Hermite functions are an orthonormal
total family of eigenvectors of `H` in `D_{a,k}`.  No relative bound and no domination is
used; the only hypothesis is invertibility of `A`, which is exactly what is needed to
solve for the classical equilibrium.

## What is proved

* `quadPolyMatT`, `foTPoly`, `shiftedHMatPoly` — the Hamiltonian in the polynomial
  coordinates of the translated, modulated frame;
* `quadPolyMatT_apply_expand` — the expansion of the quadratic part into `H_A`, a
  first-order part and a constant;
* `shiftedHMatPoly_eq_quadPolyMat` — **completing the square** in matrix form;
* `hermiteTRLp`, `orthonormal_hermiteTRLp`, `span_hermiteTRLp`, `hermiteTRLp_total` — the
  translated, modulated, rotated product Hermite functions are an orthonormal family whose
  span is the core and which is total in `L²(ℝᵈ)`;
* `shiftedHMatOp`, `shiftedHMatOp_hermiteTRLp` — the operator and its diagonal action;
* `shiftedHMatOp_symmetric`, `shiftedHMatOp_essentiallySelfAdjoint` — **the headline**, for
  every real symmetric invertible `A` of arbitrary signature;
* `shiftedHMatOp_not_bounded`, `shiftedHMatCore_dense` — non-vacuity: the operator is
  genuinely unbounded (an invertible `A` has no zero eigenvalue) and its domain is dense;
* `shiftedHMatOp_stone_flow` — the resulting complete unitary Schrödinger flow;
* `wave_rotated_linear_essentiallySelfAdjoint` — the corollary: the rotated Minkowski
  quadratic (indefinite, with cross terms) plus an arbitrary constant external field and
  boost.

## Honest boundary

Invertibility of `A` is used exactly once, to solve `A a = −2b`, `A k = −b'/2`; if `A` is
singular and `b` has a component in the kernel the square cannot be completed (the motion
is free in that direction).  Nothing here claims a general Faris–Lavine potential.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ShiftedQuadraticMatrix

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. The Hamiltonian in the translated, modulated polynomial coordinates -/

/-- The general quadratic form `∑_{p,q} A_{pq}(π_pπ_q + x_px_q/4)` in the translated,
modulated frame. -/
def quadPolyMatT (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ p, ∑ q, ((A p q : ℝ) : ℂ) •
    ((momTPoly k p).comp (momTPoly k q) + (1/4 : ℂ) • ((mulXTPoly a p).comp (mulXTPoly a q)))

/-- The first-order term `∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` in the translated, modulated frame. -/
def foTPoly (a k : Vd d) (b b' : Fin d → ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, (((b i : ℝ) : ℂ) • mulXTPoly a i + ((b' i : ℝ) : ℂ) • momTPoly k i)

/-- The full inhomogeneous quadratic Hamiltonian in the translated, modulated frame. -/
def shiftedHMatPoly (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (b b' : Fin d → ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  quadPolyMatT a k A + foTPoly a k b b'







/-! ## 2. Completing the square -/

/-- The constant produced by completing the square, `(⟨a, b⟩ + ⟨b', k⟩)/2`. -/
def matShiftConst (a k : Vd d) (b b' : Fin d → ℝ) : ℝ :=
  (∑ i, a i * b i + ∑ i, b' i * k i) / 2



/-! ## 3. The translated, modulated, rotated Hermite functions -/

/-- The translated, modulated, rotated product Hermite function, normalized in `L²`. -/
def hermiteTRLp (O : Matrix (Fin d) (Fin d) ℝ) (a k : Vd d) (α : Fin d →₀ ℕ) : L2d d :=
  ((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • pgLpT a k (rotPoly O (hermiteMv α))











/-! ## 4. The operator on the translated core, and its diagonal action -/

/-- **The inhomogeneous quadratic Hamiltonian on the translated, modulated core.** -/
def shiftedHMatOp (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (b b' : Fin d → ℝ) :
    (polyGaussCoreT a k) →ₗ[ℂ] L2d d :=
  (polyGaussCoreT a k).subtype ∘ₗ coreOpT a k (shiftedHMatPoly a k A b b')



/-! ## 5. Symmetry and essential self-adjointness -/





/-- The classical equilibrium position `a = −2A⁻¹b`. -/
def matShiftVec (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) : Vd d :=
  (WithLp.toLp 2 (A⁻¹ *ᵥ fun i => -2 * b i) : Vd d)

/-- The classical equilibrium momentum `k = −A⁻¹b'/2`. -/
def matBoostVec (A : Matrix (Fin d) (Fin d) ℝ) (b' : Fin d → ℝ) : Vd d :=
  (WithLp.toLp 2 (A⁻¹ *ᵥ fun i => -(b' i) / 2) : Vd d)



















/-! ## 6. The rotated Minkowski corollary -/







end

end BookProof.ShiftedQuadraticMatrix


