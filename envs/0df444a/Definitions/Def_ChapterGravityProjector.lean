-- Prove2me | Definitions.Def_ChapterGravityProjector
-- name    : ChapterGravityProjector
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:01:01.694129+00:00
-- url     : https://prove2.me/theorems/2d94a6fc-b48b-474a-9c46-291abc286d79
-- title:
--   Chapter GravityProjector
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGravityProjector.lean`): generated def bundle for ChapterGravityProjector. See BookProof/ChapterGravityProjector.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGravityProjector.lean

import Mathlib


/-!
# Chapter — Diffeomorphisms and gravity: the spatial projector `χ = δ + v⊗v`

Source: `book.tex`, chapter *"Diffeomorphisms and gravity"*, §*"Classical
Hamiltonian"* (line ~8091).  In the Einstein–Cartan / teleparallel Hamiltonian
formalism the author introduces, relative to a globally defined **unit timelike
vector** `v` (`vᵘ vᵤ = −1` in the mostly-plus Minkowski metric
`η = diag(−1,1,1,1)`), the mixed tensor

`χ_a{}^b = δ_a{}^b + v_a v^b`,

which is used pervasively to decompose all the torsion tensors into their
spatial (`3`-dimensional) and temporal parts.  This `χ` is exactly the
**orthogonal projector onto the spatial hyperplane** `v^⊥`: it annihilates `v`,
is idempotent, has trace `3` (it is a rank-`3` projector, the spatial slice), and
acts as the identity on vectors orthogonal to `v`.

This file makes those self-contained linear-algebra facts precise, modelling the
`(1,1)` tensor `χ^a{}_b = δ^a{}_b + v^a v_b` (raising the free index so it acts
on contravariant vectors) as an explicit `4×4` real matrix.

Formalized here (all under the physical unit-timelike hypothesis
`minkSq v = -1`, i.e. `−v₀² + v₁² + v₂² + v₃² = −1`):

* `metric` — the Minkowski metric `η = diag(−1,1,1,1)`;
* `lower v` — index lowering `v_a = η_{ab} v^b`;
* `minkSq v` — the Minkowski square `v^a v_a`;
* `spatialProj v` — the projector `χ^a{}_b = δ^a{}_b + v^a v_b`;
* `spatialProj_mulVec_self` — `χ` annihilates `v` (`v` spans the kernel);
* `spatialProj_idempotent` — `χ² = χ` (it is a genuine projector);
* `trace_spatialProj` — `tr χ = 3` (rank `3`: the spatial slice);
* `spatialProj_mulVec_of_orthogonal` — `χ` is the identity on `v^⊥`, so it is the
  orthogonal projection onto the spatial hyperplane.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterGravityProjector

open Matrix
open scoped BigOperators

/-- The Minkowski metric `η = diag(−1, 1, 1, 1)` (mostly-plus convention). -/
noncomputable def metric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

/-- Index lowering `v_a = η_{ab} v^b`. -/
noncomputable def lower (v : Fin 4 → ℝ) : Fin 4 → ℝ := metric.mulVec v

/-- The Minkowski square `v^a v_a = η_{ab} v^a v^b`. -/
noncomputable def minkSq (v : Fin 4 → ℝ) : ℝ := ∑ a, v a * lower v a

/-- The spatial projector `χ^a{}_b = δ^a{}_b + v^a v_b`, as a `4×4` matrix acting
on contravariant vectors. -/
noncomputable def spatialProj (v : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  1 + Matrix.of (fun a b => v a * lower v b)

/-
`χ` annihilates the timelike vector `v`: `χ v = 0`, so `v` spans the kernel
of the spatial projector.
-/


/-
`χ` is idempotent: `χ² = χ`, i.e. it is a genuine projector.
-/


/-
`χ` has trace `3`: it is a rank-`3` projector (the `3`-dimensional spatial
slice orthogonal to `v`).
-/


/-
`χ` acts as the identity on vectors orthogonal to `v` (`v_a x^a = 0`), so it
is the orthogonal projection onto the spatial hyperplane `v^⊥`.
-/


end BookProof.ChapterGravityProjector


