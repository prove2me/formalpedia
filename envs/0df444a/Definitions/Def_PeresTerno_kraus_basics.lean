-- Prove2me | Definitions.Def_PeresTerno_kraus_basics
-- name    : PeresTerno_kraus_basics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T23:14:08.370977+00:00
-- url     : https://prove2.me/theorems/b4b4f12c-2ee9-4670-88f1-f6f64d35b9c6
-- title:
--   Kraus update, POVM elements, density matrices, and complete positivity
-- statement:
--   Let $d$, $e$ be finite index sets and let $\{A_m\}_{m\in I}$ be a finite family of complex $e\times d$ matrices (the Kraus matrices of one outcome). This file defines:
--
--   1. the **Kraus update** of a $d\times d$ matrix $\rho$ (Eq. (6)):
--   $$\rho' = \sum_{m\in I} A_m\,\rho\,A_m^\dagger \quad (\text{an } e\times e \text{ matrix});$$
--   2. the **POVM element** (Eq. (8)):
--   $$E = \sum_{m\in I} A_m^\dagger A_m \quad (\text{a } d\times d \text{ matrix, the size of the initial state});$$
--   3. a **density matrix**: a positive semidefinite complex matrix of trace $1$;
--   4. the **ampliation** $T\otimes\mathbb 1$ of a map $T$ from $d\times d$ to $e\times e$ matrices, acting on a matrix $R$ indexed by $d\times F$ by applying $T$ to every $d\times d$ block $(R_{(i,a),(j,b)})_{i,j}$;
--   5. a **positive map**: $T(\rho)$ is positive semidefinite whenever $\rho$ is;
--   6. a **completely positive map**: $(T\otimes\mathbb 1)(R)$ is positive semidefinite for every positive semidefinite $R$ on $\mathbb C^d\otimes\mathbb C^n$, for every $n\in\mathbb N$.
--
--   These are the shared vocabulary of every statement in the mission.
--
--   **Formalization Note** The maps in items 4-6 are arbitrary functions on matrices (linearity is required separately where the source requires it). The ancilla in item 6 is indexed by `Fin n`.
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, pp. 99-100, Sec. II.D, Eqs. (6) and (8); complete positivity as defined on p. 100

import Mathlib

/-!
# Kraus operators, POVM elements, and complete positivity

Definitions for the mission drafted from A. Peres and D. R. Terno,
*Quantum information and relativity theory*, Rev. Mod. Phys. 76 (2004) 93,
Sec. II.D–II.E, Eqs. (6)–(11).
-/

namespace PeresTerno

open Matrix
open scoped ComplexOrder

/-- Eq. (6): the (unnormalized) post-measurement state
`ρ'_μ = ∑ₘ A_{μm} ρ A_{μm}†` for the Kraus matrices `A m` of one outcome `μ`.
The Kraus matrices may change the dimension (`e × d`). -/
noncomputable def krausUpdate {d e ι : Type*} [Fintype d] [Fintype ι]
    (A : ι → Matrix e d ℂ) (ρ : Matrix d d ℂ) : Matrix e e ℂ :=
  ∑ m, A m * ρ * (A m)ᴴ

/-- Eq. (8): the POVM element `E_μ = ∑ₘ A_{μm}† A_{μm}` (a `d × d` matrix, the same size
as the initial state). -/
noncomputable def povmElement {d e ι : Type*} [Fintype e] [Fintype ι]
    (A : ι → Matrix e d ℂ) : Matrix d d ℂ :=
  ∑ m, (A m)ᴴ * A m

/-- A density matrix: positive semidefinite with unit trace. -/
def IsDensityMatrix {d : Type*} [Fintype d] (ρ : Matrix d d ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The map `T ⊗ 1` acting on a bipartite matrix on `d × f`: `T` is applied to each
`d × d` block `(R_{(i,a),(j,b)})_{i,j}` indexed by the ancilla labels `a, b`. -/
def ampliate {d e f : Type*} (T : Matrix d d ℂ → Matrix e e ℂ)
    (R : Matrix (d × f) (d × f) ℂ) : Matrix (e × f) (e × f) ℂ :=
  fun p q => T (fun i j => R (i, p.2) (j, q.2)) p.1 q.1

/-- A map is positive if it sends positive semidefinite matrices to positive semidefinite
matrices. -/
def IsPositiveMap {d e : Type*} [Fintype d] [Fintype e]
    (T : Matrix d d ℂ → Matrix e e ℂ) : Prop :=
  ∀ ρ : Matrix d d ℂ, ρ.PosSemidef → (T ρ).PosSemidef

/-- A map is completely positive if `T ⊗ 1` is positive for an ancilla of every finite
dimension `n`. -/
def IsCompletelyPositive {d e : Type*} [Fintype d] [Fintype e]
    (T : Matrix d d ℂ → Matrix e e ℂ) : Prop :=
  ∀ (n : ℕ) (R : Matrix (d × Fin n) (d × Fin n) ℂ), R.PosSemidef →
    (ampliate T R).PosSemidef

end PeresTerno


