-- Prove2me | Definitions.Def_ChapterParityMajoranaQuant
-- name    : ChapterParityMajoranaQuant
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-08T01:40:33.34891+00:00
-- url     : https://prove2.me/theorems/fe11828b-b5e6-4791-940c-7ee0173337e6
-- title:
--   Parity and Majorana quantization
-- statement:
--   Formal definitions for the Parity and Majorana quantization of the timepiece Lean 4 formalization (module `BookProof.ParityMajoranaQuant`, source chapter `BookProof/ChapterParityMajoranaQuant.lean`).
--
--   This file formalizes the finite algebraic core of the subsection *"Majorana spinors in canonical quantization and antiparticles"* of the `book.tex` chapter *"On the physical parity transformation and antiparticles"* (`book.tex` line ~7680), continuing `ChapterParity` / `ChapterParityQL` / `ChapterParityHiggs`.
--
--   The book performs the canonical quantization of a **real** Hilbert (or symplectic) space `V` by introducing a *skew-symmetric* operator `J` with `J² = -1` — a **complex structure** — and splitting the self-adjoint field `a(v)` into an annihilation and a creation part,
--
--   `a(v) = a(v + iJv) + a(v − iJv)`,
--
--   where `a(v + iJv)` is an **annihilation** operator and `a(v − iJv) = a(v + iJv)*` a **creation** operator. The two combinations `v ↦ v ± iJv` are (twice) the projections onto the `∓i`-eigenspaces of `J`; on the complexification the split is governed by the two spectral projections of the Hermitian involution `iJ`.
--
--   On a finite model `V = ℂᵐ` a complex structure is a matrix `J` with `J·J = -1` that is **skew-adjoint** `Jᴴ = -J` (the complexification of a real skew-symmetric operator). We prove, `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):
--
--   * `iJ` (`= i·J`) is a **Hermitian involution**: `iJ_herm` (`(iJ)ᴴ = iJ`) and `iJ_sq` (`(iJ)² = 1`), so its eigenvalues are `±1`. * the annihilation/creation projections `annihProj = ½(1 + iJ)`, `creatProj = ½(1 − iJ)`: - `proj_add` : `annihProj + creatProj = 1` (the field split `a(v) = a₋ + a₊`); - `annihProj_idem` / `creatProj_idem` : both are idempotent; - `annih_creat_zero` / `creat_annih_zero` : `annihProj·creatProj = creatProj·annihProj = 0` (complementary projections onto the two eigenspaces); - `annihProj_herm` / `creatProj_herm` : both are Hermitian (orthogonal projections); * `J_unitary` / `J_unitary'` : a compatible complex structure is unitary (`Jᴴ·J = J·Jᴴ = 1`) — the metric/complex-structure/symplectic-form compatibility of the book's real Hilbert or symplectic space. * the eigen-relations exhibiting them as the `∓i`-eigenprojections of `J`: `J_annih` (`J·annihProj = (−i)·annihProj`) and `J_creat` (`J·creatProj = i·creatProj`) — the annihilation combination `v + iJv` lies in the `−i`-eigenspace of `J`, the creation combination `v − iJv` in the `+i`-eigenspace.
--
--   A concrete non-vacuous witness that the hypotheses are satisfiable is provided by the standard `2×2` symplectic unit `stdJ = !![0,1;−1,0]` (`stdJ_sq`, `stdJ_skew`).
--
--   The surrounding physical modelling (the abstract Clifford/CAR `C*`-algebra, the bosonic symplectic CCR `[a(v),a(w)] = ⟨v,Jw⟩i`, the vacuum functional) is left as prose, as in the neighbouring parity files.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean

import Mathlib

/-!
# Chapter "On the physical parity transformation and antiparticles" — the complex
structure `J` of canonical quantization and the creation/annihilation split

This file formalizes the finite algebraic core of the subsection *"Majorana spinors in
canonical quantization and antiparticles"* of the `book.tex` chapter *"On the physical
parity transformation and antiparticles"* (`book.tex` line ~7680), continuing
`ChapterParity` / `ChapterParityQL` / `ChapterParityHiggs`.

The book performs the canonical quantization of a **real** Hilbert (or symplectic) space
`V` by introducing a *skew-symmetric* operator `J` with `J² = -1` — a **complex structure**
— and splitting the self-adjoint field `a(v)` into an annihilation and a creation part,

  `a(v) = a(v + iJv) + a(v − iJv)`,

where `a(v + iJv)` is an **annihilation** operator and `a(v − iJv) = a(v + iJv)*` a
**creation** operator.  The two combinations `v ↦ v ± iJv` are (twice) the projections onto
the `∓i`-eigenspaces of `J`; on the complexification the split is governed by the two
spectral projections of the Hermitian involution `iJ`.

On a finite model `V = ℂᵐ` a complex structure is a matrix `J` with `J·J = -1` that is
**skew-adjoint** `Jᴴ = -J` (the complexification of a real skew-symmetric operator).  We
prove, `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):

* `iJ` (`= i·J`) is a **Hermitian involution**: `iJ_herm` (`(iJ)ᴴ = iJ`) and `iJ_sq`
  (`(iJ)² = 1`), so its eigenvalues are `±1`.
* the annihilation/creation projections `annihProj = ½(1 + iJ)`, `creatProj = ½(1 − iJ)`:
  - `proj_add` : `annihProj + creatProj = 1` (the field split `a(v) = a₋ + a₊`);
  - `annihProj_idem` / `creatProj_idem` : both are idempotent;
  - `annih_creat_zero` / `creat_annih_zero` : `annihProj·creatProj = creatProj·annihProj = 0`
    (complementary projections onto the two eigenspaces);
  - `annihProj_herm` / `creatProj_herm` : both are Hermitian (orthogonal projections);
* `J_unitary` / `J_unitary'` : a compatible complex structure is unitary (`Jᴴ·J = J·Jᴴ = 1`) —
  the metric/complex-structure/symplectic-form compatibility of the book's real Hilbert or
  symplectic space.
* the eigen-relations exhibiting them as the `∓i`-eigenprojections of `J`:
  `J_annih` (`J·annihProj = (−i)·annihProj`) and `J_creat` (`J·creatProj = i·creatProj`) —
  the annihilation combination `v + iJv` lies in the `−i`-eigenspace of `J`, the creation
  combination `v − iJv` in the `+i`-eigenspace.

A concrete non-vacuous witness that the hypotheses are satisfiable is provided by the
standard `2×2` symplectic unit `stdJ = !![0,1;−1,0]` (`stdJ_sq`, `stdJ_skew`).

The surrounding physical modelling (the abstract Clifford/CAR `C*`-algebra, the bosonic
symplectic CCR `[a(v),a(w)] = ⟨v,Jw⟩i`, the vacuum functional) is left as prose, as in the
neighbouring parity files.
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterParityMajoranaQuant

variable {m : ℕ}

/-- The Hermitian operator `iJ := i·J` associated with a complex structure `J`. -/
noncomputable def iJ (J : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Complex.I • J

/-- The **annihilation** projection `½(1 + iJ)` — its range is the `−i`-eigenspace of `J`,
spanned by the combinations `v + iJv` the book calls annihilation operators. -/
noncomputable def annihProj (J : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (1 + iJ J)

/-- The **creation** projection `½(1 − iJ)` — its range is the `+i`-eigenspace of `J`,
spanned by the combinations `v − iJv` the book calls creation operators. -/
noncomputable def creatProj (J : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (1 - iJ J)

section
variable (J : Matrix (Fin m) (Fin m) ℂ)



























end

/-! ### A concrete non-vacuous witness: the standard symplectic unit on `ℂ²`. -/

/-- The standard `2×2` symplectic unit `!![0,1;-1,0]`, a real skew-symmetric complex
structure. -/
noncomputable def stdJ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]





end BookProof.ChapterParityMajoranaQuant


