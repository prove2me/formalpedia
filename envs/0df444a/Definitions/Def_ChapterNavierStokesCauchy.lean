-- Prove2me | Definitions.Def_ChapterNavierStokesCauchy
-- name    : ChapterNavierStokesCauchy
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:24:28.752989+00:00
-- url     : https://prove2.me/theorems/19bbe691-0a8d-43c8-893c-70e22e2b347b
-- title:
--   Companion to `BookProof.ChapterNavierStokesFlow`. That module builds the truncated Navier–Stokes Hamiltonian `H_N` and i ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesCauchy`, source chapter `BookProof/ChapterNavierStokesCauchy.lean`).
--
--   Companion to `BookProof.ChapterNavierStokesFlow`. That module builds the truncated Navier–Stokes Hamiltonian `H_N` and its flow `U(t) = e^{i t H_N}` and proves that the flow is a one-parameter unitary group (so it is *complete*: it exists for every real time) which preserves the `ℓ²` mass.
--
--   This module supplies the missing *differential* half of `book.tex` ~4210–4216 ("the solution … exists and it is unique"): on the finite truncation the curve `t ↦ U(t) ψ` is differentiable and
--
--   * **solves** the evolution equation `ψ̇(t) = i H_N ψ(t)` with `ψ(0) = ψ` (`nsFlow_solves_schrodinger`), and * is the **only** solution — any differentiable curve satisfying the same equation and the same initial value coincides with it at every time (`nsFlow_unique_solution`), so the Cauchy problem is uniquely solvable for all time (`nsCauchy_existsUnique`).
--
--   Together with `nsFlow_noBlowup` of the companion module this is the honest, finite-dimensional shadow of global regularity: *on the truncation* the initial value problem has one and only one solution, defined for all `t ∈ ℝ`, whose coefficients never exceed the conserved initial mass.
--
--   Exactly as in the companion module, **nothing is claimed about the continuum Navier–Stokes equations**. The statements below are theorems about a fixed finite-dimensional truncation, where the generator is a finite Hermitian matrix; the passage to the untruncated operator (essential self-adjointness, and with it global existence and uniqueness for Navier–Stokes) is the research target recorded in `BookProof.ChapterNavierStokesFlow`, not a result of this file.
--
--   The general lemmas about `matrixFlow` are stated for an arbitrary complex square matrix, since neither differentiability nor uniqueness uses Hermiticity; only the *unitarity* of the Navier–Stokes flow does.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesCauchy.lean

import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterFreeFieldConstraint
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterU

import Mathlib
import Mathlib

import Mathlib

import Mathlib

/-!
# The truncated Navier–Stokes Cauchy problem: global existence and uniqueness

Companion to `BookProof.ChapterNavierStokesFlow`.  That module builds the
truncated Navier–Stokes Hamiltonian `H_N` and its flow `U(t) = e^{i t H_N}` and
proves that the flow is a one-parameter unitary group (so it is *complete*: it
exists for every real time) which preserves the `ℓ²` mass.

This module supplies the missing *differential* half of `book.tex` ~4210–4216
("the solution … exists and it is unique"): on the finite truncation the curve
`t ↦ U(t) ψ` is differentiable and

* **solves** the evolution equation `ψ̇(t) = i H_N ψ(t)` with `ψ(0) = ψ`
  (`nsFlow_solves_schrodinger`), and
* is the **only** solution — any differentiable curve satisfying the same
  equation and the same initial value coincides with it at every time
  (`nsFlow_unique_solution`), so the Cauchy problem is uniquely solvable for all
  time (`nsCauchy_existsUnique`).

Together with `nsFlow_noBlowup` of the companion module this is the honest,
finite-dimensional shadow of global regularity: *on the truncation* the initial
value problem has one and only one solution, defined for all `t ∈ ℝ`, whose
coefficients never exceed the conserved initial mass.

## Scope

Exactly as in the companion module, **nothing is claimed about the continuum
Navier–Stokes equations**.  The statements below are theorems about a fixed
finite-dimensional truncation, where the generator is a finite Hermitian matrix;
the passage to the untruncated operator (essential self-adjointness, and with it
global existence and uniqueness for Navier–Stokes) is the research target
recorded in `BookProof.ChapterNavierStokesFlow`, not a result of this file.

The general lemmas about `matrixFlow` are stated for an arbitrary complex square
matrix, since neither differentiability nor uniqueness uses Hermiticity; only
the *unitarity* of the Navier–Stokes flow does.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace BookProof.NavierStokesFlow

/-! ## The flow of an arbitrary finite generator -/

section MatrixFlow

variable {n : ℕ}

/-- Multiplication of a vector by a fixed matrix, as a continuous `ℝ`-linear
map.  (Everything in sight is finite-dimensional, so linearity is enough.) -/
noncomputable def mulVecCLM (A : Matrix (Fin n) (Fin n) ℂ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin A).restrictScalars ℝ)



/-- The assignment `A ↦ (x ↦ A x)` itself, as a continuous `ℝ`-linear map from
matrices to operators.  This is what turns the product rule for `t ↦ U(t) y(t)`
into an application of `HasDerivAt.clm_apply`. -/
noncomputable def mulVecCLM' :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := mulVecCLM
      map_add' := by intro A B; ext x i; simp [mulVecCLM]
      map_smul' := by intro c A; ext x i; simp [mulVecCLM, Matrix.mulVec] }



/-- Application of a fixed vector to a varying matrix, as a continuous
`ℝ`-linear map `A ↦ A x`. -/
noncomputable def applyVecCLM (x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A *ᵥ x
      map_add' := by intro A B; ext i; simp [Matrix.add_mulVec]
      map_smul' := by
        intro c A; ext i
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }



/-- The flow `t ↦ e^{t A}` generated by a finite matrix `A`. -/
noncomputable def matrixFlow (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (t • A)















end MatrixFlow

/-! ## The Navier–Stokes Cauchy problem on the truncation -/

variable {n : ℕ} (d : NSTruncation n)





















/-! ## The Lagrangian (parcel) operator generates a complete flow too

The four-term operator `ĥ_full` of Part B — positive advective Laplacian,
positive viscous term, force drift and the 0-order volume-preservation
constraint — is Hermitian on the truncation
(`LagrangianNS.transformed_hamiltonian_hermitian`), so the same argument applies
to it verbatim: its flow is a one-parameter unitary group and its Cauchy problem
is uniquely solvable for all time.  This is the truncated form of the route
recorded in Part B; the *continuum* statement remains unclaimed. -/

namespace LagrangianNS

variable (L : LagrangianNS n)

/-- The flow of the transformed (Lagrangian) operator, `e^{i t ĥ_full}`. -/
noncomputable def flowUnitary (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  matrixFlow (Complex.I • L.hFull) t







end LagrangianNS

end BookProof.NavierStokesFlow


