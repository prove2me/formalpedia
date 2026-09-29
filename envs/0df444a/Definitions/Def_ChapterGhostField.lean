-- Prove2me | Definitions.Def_ChapterGhostField
-- name    : ChapterGhostField
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-07T14:17:55.827712+00:00
-- url     : https://prove2.me/theorems/c48bb581-b0fa-4f9a-a9d1-1ab9e331f611
-- title:
--   Ghost field and BRST charge for Navier-Stokes
-- statement:
--   Formal definitions for the Ghost field and BRST charge for Navier-Stokes of the timepiece Lean 4 formalization (module `BookProof.GhostField`, source chapter `BookProof/ChapterGhostField.lean`).
--
--   Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical Field Theory and Navier-Stokes equations"*, §*"Free field parametrization in Navier-Stokes equations"* (line ~4134).
--
--   The book builds the Navier–Stokes Hilbert space as a tensor product of symmetric and antisymmetric Fock spaces, giving a graded Lie superalgebra of bosonic and fermionic creation/annihilation operators. The **divergence constraint** is imposed via a single fermionic *ghost* field `ψ` (with its space derivatives `ψ_j`), and the **BRST charge** is
--
--   ``` Ω = ∫ d³x … a†(x,…) [ u_{j,j} ψ† ] a(x,…). ```
--
--   The book specifies the ghost's canonical *anti*commutation relations and its concrete action on the two–dimensional `ℤ₂` Fock factor:
--
--   ``` {ψ, ψ†} = ψ ψ† + ψ† ψ = 1 ψ†{a}(j) = a(1) δ_{j0} ψ{a}(j) = a(0) δ_{j1} ```
--
--   This file formalizes the self-contained mathematical content of that construction:
--
--   * the single fermionic mode as the concrete `2×2` matrix model on the `ℤ₂` Fock factor `ℂ²`, its **canonical anticommutation relations** (CAR) `{ψ,ψ†} = 1`, `ψ² = 0`, `ψ†² = 0`, and `ψ† = ψᴴ`; * the ghost **number operator** `N = ψ†ψ` is an orthogonal projection (`N² = N`, `N = Nᴴ`) — the fermionic occupation is `0` or `1` (Pauli exclusion), and `N + ψψ† = 1`; * the abstract **nilpotency of the BRST charge** `Ω² = 0`, which is the reason the BRST cohomology is defined: for any operator `b` that commutes with a square-zero ghost factor `f` (`f² = 0`), the composite `Ω = b·f` satisfies `Ω² = 0`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGhostField.lean

import Mathlib

/-!
# Chapter "Free field parametrization … Navier-Stokes", §"Free field parametrization in
Navier-Stokes equations" — the fermionic ghost field and BRST charge

Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical
Field Theory and Navier-Stokes equations"*, §*"Free field parametrization in
Navier-Stokes equations"* (line ~4134).

The book builds the Navier–Stokes Hilbert space as a tensor product of symmetric
and antisymmetric Fock spaces, giving a graded Lie superalgebra of bosonic and
fermionic creation/annihilation operators.  The **divergence constraint** is
imposed via a single fermionic *ghost* field `ψ` (with its space derivatives
`ψ_j`), and the **BRST charge** is

```
Ω = ∫ d³x …  a†(x,…) [ u_{j,j} ψ† ] a(x,…).
```

The book specifies the ghost's canonical *anti*commutation relations and its
concrete action on the two–dimensional `ℤ₂` Fock factor:

```
{ψ, ψ†} = ψ ψ† + ψ† ψ = 1
ψ†{a}(j) = a(1) δ_{j0}          ψ{a}(j) = a(0) δ_{j1}
```

This file formalizes the self-contained mathematical content of that
construction:

* the single fermionic mode as the concrete `2×2` matrix model on the `ℤ₂` Fock
  factor `ℂ²`, its **canonical anticommutation relations** (CAR)
  `{ψ,ψ†} = 1`, `ψ² = 0`, `ψ†² = 0`, and `ψ† = ψᴴ`;
* the ghost **number operator** `N = ψ†ψ` is an orthogonal projection
  (`N² = N`, `N = Nᴴ`) — the fermionic occupation is `0` or `1` (Pauli
  exclusion), and `N + ψψ† = 1`;
* the abstract **nilpotency of the BRST charge** `Ω² = 0`, which is the reason
  the BRST cohomology is defined: for any operator `b` that commutes with a
  square-zero ghost factor `f` (`f² = 0`), the composite `Ω = b·f` satisfies
  `Ω² = 0`.
-/

namespace BookProof.GhostField

open Matrix

/-! ### The single fermionic mode on the `ℤ₂` Fock factor `ℂ²`

We index the two–dimensional `ℤ₂` Fock factor by `Fin 2`: index `0` is the
empty (vacuum) ghost state, index `1` the occupied ghost state.  A vector
`a : Fin 2 → ℂ` has components `a 0`, `a 1`. -/

/-- The ghost annihilation operator `ψ`: `ψ{a}(j) = a(0) δ_{j1}`, i.e. it maps
`(a₀, a₁) ↦ (0, a₀)`. -/
def psi : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The ghost creation operator `ψ†`: `ψ†{a}(j) = a(1) δ_{j0}`, i.e. it maps
`(a₀, a₁) ↦ (a₁, 0)`. -/
def psiDag : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]









/-! ### The ghost number operator -/

/-- The ghost number operator `N = ψ† ψ` (`= |1⟩⟨1|`, the occupied-state
projector). -/
noncomputable def numberOp : Matrix (Fin 2) (Fin 2) ℂ := psiDag * psi









/-! ### Nilpotency of the BRST charge

The book's BRST charge is `Ω = ∫ … [u_{j,j} ψ†]`.  The single essential
algebraic property that makes the BRST construction work is `Ω² = 0`.  Abstractly
this holds in *any* (possibly noncommutative) ring: if the ghost factor `f` is
square-zero and the bosonic factor `b` commutes with it, then `Ω = b·f`
satisfies `Ω² = 0`.  Here `f = ψ†` (square-zero by `psiDag_sq`) and `b`
represents the number-conserving field factor `u_{j,j}`. -/





end BookProof.GhostField


