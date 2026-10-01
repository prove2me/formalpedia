-- Prove2me | Definitions.Def_ChapterDensitySpectral
-- name    : ChapterDensitySpectral
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:39:52.501133+00:00
-- url     : https://prove2.me/theorems/52843e68-5b15-412e-85e7-d4480fdb3285
-- title:
--   Chapter DensitySpectral
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterDensitySpectral.lean`): generated def bundle for ChapterDensitySpectral. See BookProof/ChapterDensitySpectral.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDensitySpectral.lean

import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
the density matrix as a **diagonal probability operator rotated by a unitary**

This file formalizes the self-contained finite-dimensional content of the last
paragraph of the section *"5. Free field parametrization in Bayesian inference and
Statistical Mechanics"* (`book.tex` line ~1706), where the book states:

> *"We can always define the density matrix through a diagonal operator rotated by
> a unitary operator, with the diagonal operator defining the marginal probability
> of the initial state and the unitary operator defining the conditioned
> probability of the final state conditioned by the initial state."*

Mathematically this is the **spectral decomposition of a density matrix**: any
density matrix `ρ` (Hermitian, positive semidefinite, unit trace) equals
`ρ = U · diag(d) · U†` where `U` is unitary and `d` is its eigenvalue vector,
which is a genuine **probability distribution** — each eigenvalue is nonnegative
(positive semidefiniteness) and they sum to `1` (unit trace).  The diagonal
`d` is the "marginal probability of the initial state"; the unitary `U` (the
eigenvector rotation) is the "conditioned probability of the final state".

Everything is over `Matrix n n ℂ` for a finite index set `n`, consistently with
the finite-dimensional models used throughout `BookProof`.  All results are
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).

We prove:

* `density_eigenvalues_nonneg` — the eigenvalues of a density matrix are `≥ 0`;
* `density_eigenvalues_sum_one` — the eigenvalues sum to `1` (so together with the
  previous result they form a probability distribution);
* `density_spectral` — the spectral decomposition `ρ = U · diag(eigenvalues) · U†`
  (the "diagonal operator rotated by a unitary");
* `isDensityMatrix_of_unitary_diagonal` — the **converse**: for any unitary `U`
  and any probability distribution `d`, the matrix `U · diag(d) · U†` is a density
  matrix;
* `density_iff_exists_unitary_diagonal` — the **headline** characterization: a
  matrix is a density matrix **iff** it is a probability-diagonal operator rotated
  by a unitary.
-/

namespace BookProof.DensitySpectral

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A **density matrix**: Hermitian, positive semidefinite, of unit trace. -/
def IsDensityMatrix (ρ : Matrix n n ℂ) : Prop :=
  ρ.IsHermitian ∧ ρ.PosSemidef ∧ ρ.trace = 1











end BookProof.DensitySpectral


