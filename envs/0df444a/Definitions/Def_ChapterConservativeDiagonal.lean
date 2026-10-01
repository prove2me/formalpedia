-- Prove2me | Definitions.Def_ChapterConservativeDiagonal
-- name    : ChapterConservativeDiagonal
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:37:31.760005+00:00
-- url     : https://prove2.me/theorems/065f124f-fd56-4dfe-a25b-fa48417048cb
-- title:
--   Chapter ConservativeDiagonal
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterConservativeDiagonal.lean`): generated def bundle for ChapterConservativeDiagonal. See BookProof/ChapterConservativeDiagonal.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterConservativeDiagonal.lean

import Definitions.Def_ChapterFreeFieldConstraint
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §8 —
# the conservative double-commutator condition `[[H, P_A], P_B] = 0`

Source: `book.tex`, section *"8. Conservative transformations"* (line ~1917).

The book calls a Hamiltonian `H` **conservative** when the double commutator
`[[H, P_A], P_B] = 0` vanishes for all events `A, B ⊆ X`, where `P_A` is the
projection-valued measure of the (commutative) event algebra.  The complementary
unitary-time-evolution content of that section is in `BookProof.ChapterConservative`;
this file formalizes the algebraic **conservative condition itself**, in the
finite-dimensional model where events are subsets `S ⊆ {1, …, n}` and `P_S` is the
diagonal projection `diag(𝟙_S)` in the measurement basis.

Main results (with `⁅·,·⁆` the matrix commutator
`BookProof.FreeFieldConstraint.bracket`):

* `eventProj` — the diagonal event projection `P_S = diag(𝟙_S)`, with
  `eventProj_isDiag`, `eventProj_idem` (`P_S² = P_S`) and `eventProj_commute`
  (event projections pairwise commute, i.e. the event algebra is commutative);
* `commutes_all_events_iff_isDiag` — `H` commutes with **every** event projection
  iff `H` is diagonal;
* `conservative_iff_isDiag` — **the headline**: the conservative double-commutator
  condition `∀ S T, ⁅⁅H, P_S⁆, P_T⁆ = 0` holds iff `H` is diagonal.

Thus in finite dimensions the conservative condition is exactly as strong as full
commutation with the event algebra (`H` diagonal): the *only* conservative
Hamiltonians are the classical/diagonal ones.  This is the finite-dimensional
counterpart of the book's remark, and pinpoints why the book's genuinely
non-diagonal conservative Hamiltonians (`H = Σ_j p_j⁅H,x_j⁆ + ⁅H,x_j⁆p_j`,
built from momentum operators) require a *continuous* spectrum: there `⁅H, P_A⁆`
becomes a multiplication (diagonal) operator supported on the boundary `∂A`, which
then commutes with every `P_B`, an escape that has no finite-dimensional analogue.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped Matrix
open Matrix BookProof.FreeFieldConstraint

namespace BookProof.ConservativeDiagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal **event projection** `P_S = diag(𝟙_S)` onto the coordinates of an
event (subset) `S ⊆ {1, …, n}`, in the measurement basis. -/
noncomputable def eventProj (S : Finset n) : Matrix n n ℂ :=
  Matrix.diagonal (fun k => if k ∈ S then (1 : ℂ) else 0)















end BookProof.ConservativeDiagonal


