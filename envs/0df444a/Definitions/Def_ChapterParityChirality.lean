-- Prove2me | Definitions.Def_ChapterParityChirality
-- name    : ChapterParityChirality
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:23:20.488195+00:00
-- url     : https://prove2.me/theorems/386865de-aed5-421c-bed4-11fad018ff01
-- title:
--   Chapter ParityChirality
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterParityChirality.lean`): generated def bundle for ChapterParityChirality. See BookProof/ChapterParityChirality.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityChirality.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
import Mathlib


/-!
# Chapter "On the physical parity transformation and antiparticles" — the chirality
projector in the left-handed quark doublet `Q_L`

This file continues the finite algebraic core of the `book.tex` chapter *"On the physical
parity transformation and antiparticles"* (`book.tex` line ~7522, §"Majorana spinors in
the Standard Model"), begun in `ChapterParity`/`ChapterParityQL`/`ChapterParitySU2`.

The chapter states that the left-handed quark doublet `Q_L` — a Majorana (real) spinor
carrying **both** an `SU(2)_L` doublet index and a Majorana spinor index — satisfies the
chirality/projection constraint

  `i γ⁵ Q_L = i σ₃ Q_L`,

with the `SU(2)_L` factor `i σ₃` acting on the doublet index (`ℂ²`) and the internal
`U(1)_Y`/chirality generator `i γ⁵ = mgamma5` acting on the spinor index (`ℂ⁴`).  A
footnote then uses "the **projector in `Q_L`**" to halve the count of the
`SU(2)_L`-invariant Yukawa products (the `4` custodial matrices `{1, iσⱼ}` of
`ChapterParityCustodial` "divided by `2`", leaving `2` independent products).

On `ℂ² ⊗ ℂ⁴ ≅ ℂ⁸`, write `iσ₃ = (iσ₃)⊗1` (`isigma3`) and `iγ⁵ = 1⊗(iγ⁵)` (`igamma5`).
Both square to `-1` and commute, their product being the **chirality operator**
`χ = (iσ₃)⊗(iγ⁵)` (`chi`).  This file proves:

* `isigma3_sq`, `igamma5_sq`: `(iσ₃)² = (iγ⁵)² = -1` (from `pauli3² = 1`, `(iγ⁵)² = -1`);
* `isigma3_igamma5`, `igamma5_isigma3`: `iσ₃` and `iγ⁵` commute, both products equalling `χ`;
* `chi_sq`: `χ² = 1` — `χ` is an involution, so its eigenvalues are `±1`;
* `chi_trace`: `tr χ = 0` — the two eigenspaces have equal dimension (`4` and `4`), the
  "divide by `2`" of the footnote;
* `QLProj` `= ½(1 - χ)`, the projector onto the `Q_L` chirality subspace, with
  `QLProj_idem` (`P² = P`) and `QLProj_trace` (`tr P = 4`, half of `dim = 8`);
* `chirality_iff`: the book's constraint `iσ₃ Q_L = iγ⁵ Q_L` is equivalent to
  `χ Q_L = -Q_L`;
* `chirality_iff_proj`: equivalently, `Q_L` lies in the range of the projector,
  `P Q_L = Q_L`.

The surrounding physical modelling (the full Standard-Model Yukawa Lagrangian and the
`SU(2)_L × (SU(3)_C × U(1)_Y) ⋊ ℤ₄` background symmetry) is left as prose.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix
open scoped Kronecker

namespace BookProof.ChapterParityChirality

open BookProof.ChapterA3
open BookProof.ChapterParity
open BookProof.ChapterParitySU2

/-- `iσ₃` acting on the `SU(2)_L` doublet index, extended to `ℂ²⊗ℂ⁴` as `(iσ₃)⊗1`. -/
noncomputable def isigma3 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  (Complex.I • pauli3) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- `iγ⁵` acting on the Majorana spinor index, extended to `ℂ²⊗ℂ⁴` as `1⊗(iγ⁵)`. -/
noncomputable def igamma5 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ mgamma5

/-- The **chirality operator** `χ = (iσ₃)⊗(iγ⁵)` on `ℂ²⊗ℂ⁴ ≅ ℂ⁸`. -/
noncomputable def chi : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  (Complex.I • pauli3) ⊗ₖ mgamma5













/-- The **`Q_L` chirality projector** `P = ½(1 - χ)` onto the `χ = -1` eigenspace, i.e. the
subspace where the chapter's constraint `iσ₃ Q_L = iγ⁵ Q_L` holds. -/
noncomputable def QLProj : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  (2 : ℂ)⁻¹ • (1 - chi)









end BookProof.ChapterParityChirality


