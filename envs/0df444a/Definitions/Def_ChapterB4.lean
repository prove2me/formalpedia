-- Prove2me | Definitions.Def_ChapterB4
-- name    : ChapterB4
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:42:58.346451+00:00
-- url     : https://prove2.me/theorems/f8a21d68-d2d7-4e3a-bc0a-d63976a5f8ab
-- title:
--   Chapter B4
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterB4.lean`): generated def bundle for ChapterB4. See BookProof/ChapterB4.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterB4.lean

import Mathlib


/-!
# Chapter B4 — The Gleason contrast: pure vs. mixed states on non-commuting projections

Source: `book.tex` §4 (line ~1637, "Quantum Mechanics versus a non-commutative
generalization of probability theory").  The book compares its commuting
(wave-function) parametrization with Gleason's theorem, which parametrizes
probability assignments to *non-commuting* projections by a (possibly mixed)
density matrix.  The `2`-dimensional real worked example is a concrete,
finite-dimensional, fully self-contained statement flagged in
`FORMALIZATION_ROADMAP.md` (Chapter B remark) as "worth adding as a sanity
check".  This file formalizes it.

Fix the two non-commuting real projections
`P₁ = [[1,0],[0,0]]` and `P₂ = ½[[1,1],[1,1]]`.  A **pure state** in the
`2`-dimensional real case is a rank-one projector `v vᵀ` for a unit vector `v`
(`IsPureState`); a **density matrix** is a Hermitian, positive-semidefinite,
unit-trace matrix (`IsDensityMatrix`).  The Born value assigned to a projection
`P` by a state `ρ` is `tr(ρ P)`.  The results:

* `pure_state_satisfies_P1` — a pure state (namely `P₂` itself) gives
  `tr(ρ P₁) = ½`;
* `pure_state_satisfies_P2` — a pure state (namely `P₁` itself) gives
  `tr(ρ P₂) = ½`;
* **headline** `no_pure_state_satisfies_both` — **no** pure state gives
  `tr(ρ P₁) = ½` *and* `tr(ρ P₂) = ½` simultaneously;
* `mixed_state_satisfies_both` — the mixed state `ρ = ½ I` *does* satisfy both,
  and `mixed_state_not_pure` shows it is genuinely mixed (not pure), while
  `mixed_state_isDensityMatrix` confirms it is a legitimate density matrix.

This is exactly the book's point: the wave-function (pure states) cannot match
the Born data of two non-commuting projections at once, whereas Gleason's
mixed-state density matrix can.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterB4

open Matrix

noncomputable section

/-- The projection `P₁ = |1⟩⟨1| = [[1,0],[0,0]]`. -/
def P1 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The projection `P₂ = ½[[1,1],[1,1]]` (onto the `(1,1)/√2` direction). -/
def P2 : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; 1/2, 1/2]

/-- A **pure state** in the `2`-dimensional real case: the rank-one projector
`ρ = v vᵀ` associated to a real unit vector `v`. -/
def IsPureState (ρ : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ v : Fin 2 → ℝ, v 0 ^ 2 + v 1 ^ 2 = 1 ∧ ρ = fun i j => v i * v j

/-- A **density matrix**: Hermitian, positive-semidefinite, unit trace. -/
def IsDensityMatrix (ρ : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ρ.IsHermitian ∧ ρ.PosSemidef ∧ Matrix.trace ρ = 1

















end

end BookProof.ChapterB4


