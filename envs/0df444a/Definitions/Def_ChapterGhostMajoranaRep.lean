-- Prove2me | Definitions.Def_ChapterGhostMajoranaRep
-- name    : ChapterGhostMajoranaRep
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:06:15.875646+00:00
-- url     : https://prove2.me/theorems/edf75deb-3b0e-48a7-a4ac-6322cf1b1e99
-- title:
--   Chapter GhostMajoranaRep
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGhostMajoranaRep.lean`): generated def bundle for ChapterGhostMajoranaRep. See BookProof/ChapterGhostMajoranaRep.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGhostMajoranaRep.lean

import Definitions.Def_ChapterGhostField
import Mathlib

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/

/-!
# The two presentations of the ghost algebra: fermionic (`ψ, ψ†`) and self-adjoint (Majorana)

Source: `book.tex`, §*"Relation with the BRST formalism"* of the Yang–Mills
chapter (lines 6940–6960):

> "there are two representations of the ghost algebra: one degenerate where
> the ghost fields are self-adjoint and another non-degenerate where the ghost
> fields are not self-adjoint and behave like standard fermionic [fields] …
> the ghosts are as consistent as a Schrödinger field."

This file formalizes the relation between the two presentations on the `ℤ₂`
ghost fibre of `BookProof.ChapterGhostField`:

* the **fermionic** presentation `ψ, ψ†` with `{ψ, ψ†} = 1`, `ψ² = (ψ†)² = 0`,
  where `ψ` is *not* self-adjoint;
* the **self-adjoint (Majorana)** presentation `χ₁ = ψ + ψ†`,
  `χ₂ = i (ψ − ψ†)`, whose generators *are* self-adjoint and satisfy the
  Clifford relations `χ_a χ_b + χ_b χ_a = 2 δ_{ab}`.

The change of basis is invertible, so the two presentations generate the same
operator algebra: nothing physical distinguishes them, which is the book's
point that the ghost sector is as consistent as an ordinary fermionic field.

## Main results

* `psi_not_selfAdjoint` — the fermionic generator is not self-adjoint.
* `chi1_selfAdjoint`, `chi2_selfAdjoint` — the Majorana generators are.
* `chi1_sq`, `chi2_sq`, `chi_anticomm` — the Clifford relations.
* `psi_of_chi`, `psiDag_of_chi` — the inverse change of basis, so the two
  presentations generate the same algebra.
-/

namespace BookProof.ChapterGhostMajoranaRep

open Matrix BookProof.GhostField



/-- The first Majorana (self-adjoint) ghost generator `χ₁ = ψ + ψ†`. -/
def chi1 : Matrix (Fin 2) (Fin 2) ℂ := psi + psiDag

/-- The second Majorana (self-adjoint) ghost generator `χ₂ = i (ψ − ψ†)`. -/
noncomputable def chi2 : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (psi - psiDag)















end BookProof.ChapterGhostMajoranaRep


