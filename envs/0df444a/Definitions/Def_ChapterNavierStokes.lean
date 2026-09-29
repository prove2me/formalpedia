-- Prove2me | Definitions.Def_ChapterNavierStokes
-- name    : ChapterNavierStokes
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-07T14:18:46.540032+00:00
-- url     : https://prove2.me/theorems/30b2ae29-b674-49c3-83c1-9b7b336d7db7
-- title:
--   Navier-Stokes ghost CAR algebra
-- statement:
--   Formal definitions for the Navier-Stokes ghost CAR algebra of the timepiece Lean 4 formalization (module `BookProof.NavierStokes`, source chapter `BookProof/ChapterNavierStokes.lean`).
--
--   This file formalizes the self-contained mathematical content of the section *"Free field parametrization in Navier–Stokes equations"* (`book.tex` line ~4134). There the Hilbert space is a tensor product of a symmetric and an antisymmetric Fock space, and the **divergence constraint** of the Navier–Stokes equations is implemented à la BRST through a *fermionic ghost field* `ψ` (the BRST charge is `Ω = ∫ u_{j,j} ψ†`). The single ghost mode is governed by the **canonical anticommutation relation (CAR)**
--
--   > `{ψ, ψ†} = ψ ψ† + ψ† ψ = 1`,
--
--   together with the explicit realization the book writes down (`book.tex` line ~4128):
--
--   > `ψ†{a}(t, …, j) = a(t, …, 1) δ_{j0}`, `ψ{a}(t, …, j) = a(t, …, 0) δ_{j1}`.
--
--   The single-mode ghost factor is the two-dimensional occupation space `ℂ²` (`j = 0`: no ghost, `j = 1`: one ghost). Acting on a column vector `f : Fin 2 → ℂ` the book's operators are exactly the `2×2` matrices
--
--   * `ghostAnnih` (`ψ`): `(ψ f) 0 = 0`, `(ψ f) 1 = f 0` — the matrix `!![0,0;1,0]`; * `ghostCreate` (`ψ†`): the conjugate transpose `ψᴴ`, i.e. `!![0,1;0,0]`, so `(ψ† f) 0 = f 1`, `(ψ† f) 1 = 0`.
--
--   We prove, all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):
--
--   * `ghostCreate_eq` — the explicit matrix form of `ψ†`; * `ghostCreate_eq_conjTranspose` — `ψ†` **is** the (conjugate-transpose) adjoint of `ψ`, so the CAR pair really is an operator/adjoint pair; * `ghost_CAR` — the canonical anticommutation relation `ψ ψ† + ψ† ψ = 1` (the book's `{ψ, ψ†} = 1`); * `ghostAnnih_sq` / `ghostCreate_sq` — nilpotency `ψ² = 0`, `ψ†² = 0` (the fermionic **Pauli exclusion**: one cannot create or destroy two ghosts); * `ghostAnticomm_annih` / `ghostAnticomm_create` — `{ψ, ψ} = 0`, `{ψ†, ψ†} = 0`; * `ghostNumber_eq` — the number operator `N = ψ† ψ = !![1,0;0,0]`; * `ghostNumber_hermitian` — `N` is Hermitian (`Nᴴ = N`); * `ghostNumber_idem` — `N² = N`, so `N` is a projection with eigenvalues `0, 1` (fermionic occupation numbers), and dually `ψ ψ† = !![0,0;0,1]`, `N + ψ ψ† = 1` is the resolution of the identity into the two occupation sectors.
--
--   The surrounding physical construction (the graded Lie superalgebra on the full Fock space, essential self-adjointness of the polynomial Navier–Stokes Hamiltonian, and the existence/uniqueness claim) is field-theoretic modelling that is out of scope for a self-contained Lean statement; what is formalized here is the exact fermionic-ghost algebra the BRST implementation rests on.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokes.lean

import Mathlib

/-!
# Chapter "Free field parametrization in Classical Statistical Field Theory and
Navier–Stokes equations" — the BRST **ghost field** CAR algebra

This file formalizes the self-contained mathematical content of the section
*"Free field parametrization in Navier–Stokes equations"* (`book.tex` line
~4134).  There the Hilbert space is a tensor product of a symmetric and an
antisymmetric Fock space, and the **divergence constraint** of the
Navier–Stokes equations is implemented à la BRST through a *fermionic ghost
field* `ψ` (the BRST charge is `Ω = ∫ u_{j,j} ψ†`).  The single ghost mode is
governed by the **canonical anticommutation relation (CAR)**

> `{ψ, ψ†} = ψ ψ† + ψ† ψ = 1`,

together with the explicit realization the book writes down
(`book.tex` line ~4128):

> `ψ†{a}(t, …, j) = a(t, …, 1) δ_{j0}`,  `ψ{a}(t, …, j) = a(t, …, 0) δ_{j1}`.

The single-mode ghost factor is the two-dimensional occupation space
`ℂ²` (`j = 0`: no ghost, `j = 1`: one ghost).  Acting on a column vector
`f : Fin 2 → ℂ` the book's operators are exactly the `2×2` matrices

* `ghostAnnih` (`ψ`): `(ψ f) 0 = 0`, `(ψ f) 1 = f 0`  — the matrix `!![0,0;1,0]`;
* `ghostCreate` (`ψ†`): the conjugate transpose `ψᴴ`, i.e. `!![0,1;0,0]`, so
  `(ψ† f) 0 = f 1`, `(ψ† f) 1 = 0`.

We prove, all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`):

* `ghostCreate_eq` — the explicit matrix form of `ψ†`;
* `ghostCreate_eq_conjTranspose` — `ψ†` **is** the (conjugate-transpose) adjoint
  of `ψ`, so the CAR pair really is an operator/adjoint pair;
* `ghost_CAR` — the canonical anticommutation relation `ψ ψ† + ψ† ψ = 1`
  (the book's `{ψ, ψ†} = 1`);
* `ghostAnnih_sq` / `ghostCreate_sq` — nilpotency `ψ² = 0`, `ψ†² = 0`
  (the fermionic **Pauli exclusion**: one cannot create or destroy two ghosts);
* `ghostAnticomm_annih` / `ghostAnticomm_create` — `{ψ, ψ} = 0`, `{ψ†, ψ†} = 0`;
* `ghostNumber_eq` — the number operator `N = ψ† ψ = !![1,0;0,0]`;
* `ghostNumber_hermitian` — `N` is Hermitian (`Nᴴ = N`);
* `ghostNumber_idem` — `N² = N`, so `N` is a projection with eigenvalues `0, 1`
  (fermionic occupation numbers), and dually `ψ ψ† = !![0,0;0,1]`,
  `N + ψ ψ† = 1` is the resolution of the identity into the two occupation
  sectors.

The surrounding physical construction (the graded Lie superalgebra on the full
Fock space, essential self-adjointness of the polynomial Navier–Stokes
Hamiltonian, and the existence/uniqueness claim) is field-theoretic modelling
that is out of scope for a self-contained Lean statement; what is formalized
here is the exact fermionic-ghost algebra the BRST implementation rests on.
-/

namespace BookProof.NavierStokes

open Matrix

/-- The ghost **annihilation** operator `ψ` on the two-dimensional occupation
space `ℂ²` (`j = 0`: no ghost, `j = 1`: one ghost), acting on a column vector
`f : Fin 2 → ℂ` by `(ψ f) 0 = 0`, `(ψ f) 1 = f 0`.  This is the book's
`ψ{a}(…, j) = a(…, 0) δ_{j1}` (`book.tex` line ~4128). -/
noncomputable def ghostAnnih : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The ghost **creation** operator `ψ†`, defined as the (conjugate-transpose)
adjoint of `ψ`.  This makes `ψ†` genuinely the adjoint of the annihilation
operator; `ghostCreate_eq` computes its explicit matrix. -/
noncomputable def ghostCreate : Matrix (Fin 2) (Fin 2) ℂ := ghostAnnihᴴ















/-- The ghost **number operator** `N = ψ† ψ = !![1,0;0,0]`. -/
noncomputable def ghostNumber : Matrix (Fin 2) (Fin 2) ℂ := ghostCreate * ghostAnnih











end BookProof.NavierStokes


