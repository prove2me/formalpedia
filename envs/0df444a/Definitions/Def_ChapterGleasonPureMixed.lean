-- Prove2me | Definitions.Def_ChapterGleasonPureMixed
-- name    : ChapterGleasonPureMixed
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:06:54.760111+00:00
-- url     : https://prove2.me/theorems/0aeb24dc-ac33-4732-a69a-e86b0c7db5ac
-- title:
--   Chapter GleasonPureMixed
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGleasonPureMixed.lean`): generated def bundle for ChapterGleasonPureMixed. See BookProof/ChapterGleasonPureMixed.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGleasonPureMixed.lean

import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §4
*"Quantum Mechanics versus a non-commutative generalization of probability
theory"* — the 2-dimensional real pure-state vs. mixed-state (Gleason) contrast

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"*, §4 (`book.tex` line ~1550).

The book contrasts its own result (a probability measure over *commuting*
projections is always parametrized by a **wave-function**, i.e. a **pure**
state) with Gleason's theorem (a probability measure over *non-commuting*
projections needs a general **density matrix**, i.e. a possibly **mixed**
state).  It works out the difference explicitly in the *2-dimensional real*
case, with the two non-commuting projections

* `P0 = [[1,0],[0,0]]` — a diagonal (position-type) projection, and
* `Q  = ½[[1,1],[1,1]]` — the projection onto `(1,1)/√2` (momentum-type),

which do not commute.  The book's claims, formalized here over
`Matrix (Fin 2) (Fin 2) ℝ` with the expectation `E ρ A = tr(ρ A)`:

* `exists_pure_expP0` — there **is** a pure state `ρ` with `tr(ρ P0) = ½`
  (e.g. `ρ = Q`), and `exists_pure_expQ` — there **is** a pure state `ρ` with
  `tr(ρ Q) = ½` (e.g. `ρ = P0`);
* **headline** `no_pure_state_both` — there is **no** pure state `ρ` satisfying
  *both* `tr(ρ P0) = ½` and `tr(ρ Q) = ½` simultaneously (the wave-function
  cannot assign the "constant density ½" values to two non-commuting
  projections at once);
* **headline** `exists_mixed_state_both` — but there **is** a mixed state `ρ`
  (e.g. the maximally mixed `ρ = ½·I`) with both `tr(ρ P0) = ½` and
  `tr(ρ Q) = ½`, exactly as Gleason's theorem provides;
* `halfI_not_pure` — the witness `½·I` is genuinely mixed (not a pure state).

A *pure state* is a real symmetric idempotent of unit trace (an orthogonal
projection onto a line, i.e. `ρ = v vᵀ` for a real unit vector `v`); a *mixed
state* is a positive-semidefinite matrix of unit trace (a general density
matrix).  Note the restriction to **real** matrices is the book's own ("the
2-dimensional real case"): over `ℂ` the state
`[[½, i/2],[-i/2, ½]]` is pure and satisfies both constraints, so
`no_pure_state_both` is a genuinely real-field phenomenon.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

open scoped BigOperators
open Matrix

namespace BookProof.ChapterGleasonPureMixed

/-- The diagonal (position-type) projection `P0 = [[1,0],[0,0]]`. -/
noncomputable def P0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The projection `Q = ½[[1,1],[1,1]]` onto `(1,1)/√2` (momentum-type). -/
noncomputable def Q : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; 1/2, 1/2]

/-- `E ρ A = tr(ρ A)`, the expectation of the observable `A` in the state `ρ`. -/
noncomputable def E (ρ A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (ρ * A).trace

/-- A **pure state** (wave-function): a real symmetric idempotent of unit trace,
i.e. an orthogonal projection onto a line `ρ = v vᵀ`. -/
def IsPureState (ρ : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ρᵀ = ρ ∧ ρ * ρ = ρ ∧ ρ.trace = 1

/-- A **mixed state** (density matrix): a positive-semidefinite matrix of unit
trace. -/
def IsMixedState (ρ : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

























end BookProof.ChapterGleasonPureMixed


