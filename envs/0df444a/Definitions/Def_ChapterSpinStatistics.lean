-- Prove2me | Definitions.Def_ChapterSpinStatistics
-- name    : ChapterSpinStatistics
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:55:23.185826+00:00
-- url     : https://prove2.me/theorems/d1e0c914-7c42-4869-9dab-8e71052fb578
-- title:
--   Chapter SpinStatistics
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSpinStatistics.lean`): generated def bundle for ChapterSpinStatistics. See BookProof/ChapterSpinStatistics.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSpinStatistics.lean

import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §6 —
the **two-mode fermionic CAR algebra** for a finite sample space
(`ℤ₂ × ℤ₂`) and the spin–statistics dichotomy

This file formalizes the self-contained mathematical content of the section
*"6. Free field parametrization for finite sample spaces and the spin-statistics
theorem"* (`book.tex` line ~1816).  There the book observes that a finite sample
space such as `ℤ₂` is parametrized by a **fermionic** Fock space
`Γ^a(L²(ℤ₂))`, and that for a *product* `ℤ₂ × ℤ₂` one must take the graded
tensor product `Γ^s(L²(ℤ₂)) ⊗ Γ^a(L²(ℤ₂))` so that the two modes do **not**
produce spurious non-null products of creation operators — i.e. the two
fermionic modes must **anticommute**.  This anticommutation (as opposed to the
commutation of bosonic modes) is exactly the algebraic content underlying the
**spin–statistics** correspondence the section is about.

The single-mode ghost/fermion CAR `{ψ, ψ†} = 1` on `ℂ²` is already in
`BookProof/ChapterNavierStokes.lean`.  This file builds the **two-mode**
fermionic Fock space `ℂ⁴ ≅ ℂ² ⊗ ℂ²` via the Jordan–Wigner realization

* mode 1: `b₁ = a ⊗ I`,
* mode 2: `b₂ = Z ⊗ a`,   with `a = !![0,1;0,0]` the single-mode annihilation and
  `Z = diag(1,-1)` the fermion-parity string,

which on `ℂ⁴` (basis order `|n₁ n₂⟩ = |00⟩, |01⟩, |10⟩, |11⟩`, `|00⟩` the vacuum)
are the explicit `4×4` matrices

* `fermiAnnih1` (`b₁`) `= !![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0]`,
* `fermiAnnih2` (`b₂`) `= !![0,1,0,0; 0,0,0,0; 0,0,0,-1; 0,0,0,0]`,

with creation operators the conjugate-transpose (adjoint) `bᵢ†`.

We prove, all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`):

* `fermiCreate1_eq` / `fermiCreate2_eq` — the explicit matrix form of `b₁†`, `b₂†`;
* `fermi_CAR₁` / `fermi_CAR₂` — the diagonal CAR `{bᵢ, bᵢ†} = 1`;
* `fermi_CAR_cross` / `fermi_CAR_cross'` — the **off-diagonal** CAR
  `{b₁, b₂†} = 0`, `{b₂, b₁†} = 0` (distinct modes are canonically anticommuting);
* `fermiAnticomm_annih` / `fermiAnticomm_create` — `{b₁, b₂} = 0`, `{b₁†, b₂†} = 0`
  (the **fermionic statistics**: the two modes anticommute, so
  `b₁ b₂ = - b₂ b₁`);
* `fermiAnnih₁_sq` … `fermiCreate₂_sq` — nilpotency `bᵢ² = 0`, `bᵢ†² = 0`
  (Pauli exclusion per mode);
* `fermiNumber₁_eq` / `fermiNumber₂_eq` — the mode number operators
  `Nᵢ = bᵢ† bᵢ`, with `fermiNumber₁_hermitian`/`fermiNumber₁_idem` (each is a
  Hermitian projection with eigenvalues `0,1`) and `fermiNumber_commute`
  (`N₁ N₂ = N₂ N₁`, so occupation numbers are simultaneously measurable);
* `fermiTotalNumber_eq` — the total number operator `N = N₁ + N₂ = diag(0,1,1,2)`
  counts the fermionic occupation of the two-mode Fock space `ℂ⁴`.

The point of the section — that this fermionic (anticommuting) parametrization is
genuinely distinct from the bosonic (commuting) one, and that certain symmetry
transformations are representable only by one or the other (the spin–statistics
theorem) — is a representation-theoretic statement left as prose; what is
formalized here is the exact two-mode CAR algebra it rests on.
-/

namespace BookProof.SpinStatistics

open Matrix

/-- Mode-1 fermionic **annihilation** operator `b₁ = a ⊗ I` on the two-mode
Fock space `ℂ⁴ ≅ ℂ² ⊗ ℂ²`.  Basis order `|n₁ n₂⟩ = |00⟩,|01⟩,|10⟩,|11⟩`, with
`|00⟩` the vacuum; `b₁` lowers the mode-1 occupation. -/
noncomputable def fermiAnnih1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0]

/-- Mode-2 fermionic **annihilation** operator `b₂ = Z ⊗ a` (Jordan–Wigner:
the fermion-parity string `Z = diag(1,-1)` on mode 1 makes the two modes
anticommute). -/
noncomputable def fermiAnnih2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,1,0,0; 0,0,0,0; 0,0,0,-1; 0,0,0,0]

/-- Mode-1 **creation** operator `b₁†`, the (conjugate-transpose) adjoint of `b₁`. -/
noncomputable def fermiCreate1 : Matrix (Fin 4) (Fin 4) ℂ := fermiAnnih1ᴴ

/-- Mode-2 **creation** operator `b₂†`, the (conjugate-transpose) adjoint of `b₂`. -/
noncomputable def fermiCreate2 : Matrix (Fin 4) (Fin 4) ℂ := fermiAnnih2ᴴ





























/-- Mode-1 **number operator** `N₁ = b₁† b₁`. -/
noncomputable def fermiNumber1 : Matrix (Fin 4) (Fin 4) ℂ := fermiCreate1 * fermiAnnih1

/-- Mode-2 **number operator** `N₂ = b₂† b₂`. -/
noncomputable def fermiNumber2 : Matrix (Fin 4) (Fin 4) ℂ := fermiCreate2 * fermiAnnih2

















end BookProof.SpinStatistics


