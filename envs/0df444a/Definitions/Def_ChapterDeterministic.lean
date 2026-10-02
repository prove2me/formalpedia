-- Prove2me | Definitions.Def_ChapterDeterministic
-- name    : ChapterDeterministic
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:09:23.574585+00:00
-- url     : https://prove2.me/theorems/9407c013-3bf2-4f65-8065-93879534d5c2
-- title:
--   Chapter Deterministic
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterDeterministic.lean`): generated def bundle for ChapterDeterministic. See BookProof/ChapterDeterministic.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDeterministic.lean

import Definitions.Def_ChapterReconstruct
import Definitions.Def_ChapterTimeTranslation
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §9
*"Deterministic transformations"* — the commutation criterion for determinism

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"*, §9 *"Deterministic transformations"* (`book.tex` line ~1958).

The book's headline result of that section is:

> *"We conclude that an automorphism `U` is deterministic if and only if `P_A`
> and `U P_B U†` commute for all events `A, B`."*

Here `P_A ∈ L^∞(X,μ)` is the (diagonal) projection-valued measure attached to an
event `A ⊆ X`, and `U` is a unitary automorphism.  In the finite-dimensional
measurement basis `Fin n`, `L^∞` is the algebra of diagonal matrices, a single
outcome `a` corresponds to the rank-one projection `P_a = |e_a⟩⟨e_a|`
(`ChapterTimeTranslation.proj`), a general event `A ⊆ {0,…,n-1}` to
`P_A = ∑_{a∈A} P_a`, and the transformed measurement operator is
`U P_B U†` (`ChapterTimeTranslation.measOp` for a single outcome).

`U` being *deterministic* means, exactly as in `ChapterReconstruct`, that every
column of `U` has at most one nonzero entry (a permutation matrix up to phases):
the automorphism `P_A ↦ U† P_A U` maps diagonal projections to diagonal
projections, i.e. points of the spectrum of `L^∞` one-to-one to points of the
spectrum of `L^∞`.

This file supplies the **commutation layer** on top of the off-diagonal-Born
core of `ChapterReconstruct`:

* `commute_proj_measOp_iff_isDeterministicCol` — for a fixed outcome `b`, the
  rank-one projections `P_a` commute with `U P_b U†` for **all** `a` iff column
  `b` of `U` is deterministic;
* **headline** `commute_proj_measOp_iff_isDeterministic` — `P_a` and `U P_b U†`
  commute for all single outcomes `a, b` iff `U` is deterministic;
* `projSet` / `measOpSet` — event projections `P_A = ∑_{a∈A} P_a` and the
  transformed event operator `U P_B U†`, with `measOpSet_eq_sum`;
* **headline (event form)** `commute_projSet_measOpSet_iff_isDeterministic` — the
  literal book statement: `P_A` and `U P_B U†` commute for **all events**
  `A, B ⊆ {0,…,n-1}` iff `U` is deterministic.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation

namespace BookProof.ChapterDeterministic

variable {n : ℕ}

/-
Entries of `P_a · (U P_b U†)`: nonzero only in row `a`, where it equals
`U a b · conj(U j b)`.
-/


/-
Entries of `(U P_b U†) · P_a`: nonzero only in column `a`, where it equals
`U i b · conj(U a b)`.
-/


/-
**Per-column criterion.** For a fixed outcome `b`, the rank-one projections
`P_a` commute with the transformed measurement operator `U P_b U†` for every
outcome `a` iff column `b` of `U` is deterministic (at most one nonzero entry).
-/


/-
**Headline (single-outcome form).** The projections `P_a` and the transformed
measurement operators `U P_b U†` commute for all outcomes `a, b` iff `U` is
deterministic (a permutation matrix up to phases).  This is the book's criterion
*"an automorphism `U` is deterministic if and only if `P_A` and `U P_B U†`
commute for all events `A, B`"* specialized to single-outcome events.
-/


/-- The event projection `P_A = ∑_{a∈A} P_a` for an event `A ⊆ {0,…,n-1}`
(a diagonal element of `L^∞`). -/
noncomputable def projSet (A : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ a ∈ A, proj a

/-- The transformed event measurement operator `U P_B U†`. -/
noncomputable def measOpSet (U : Matrix (Fin n) (Fin n) ℂ) (B : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  U * projSet B * Uᴴ

/-
The transformed event operator is the sum of the single-outcome ones:
`U P_B U† = ∑_{b∈B} U P_b U†`.
-/


/-
**Headline (event form — the literal book statement).** For a unitary
automorphism `U`, the event projections `P_A` and the transformed event operators
`U P_B U†` commute for **all events** `A, B ⊆ {0,…,n-1}` iff `U` is deterministic.
This is exactly *"an automorphism `U` is deterministic if and only if `P_A` and
`U P_B U†` commute for all events `A, B`."*
-/


end BookProof.ChapterDeterministic


