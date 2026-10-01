-- Prove2me | Definitions.Def_ChapterGravityTimeProj
-- name    : ChapterGravityTimeProj
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T08:43:28.826772+00:00
-- url     : https://prove2.me/theorems/8cc43bf8-0d8f-4fba-8441-611dbf7ca604
-- title:
--   Chapter GravityTimeProj
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGravityTimeProj.lean`): generated def bundle for ChapterGravityTimeProj. See BookProof/ChapterGravityTimeProj.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGravityTimeProj.lean

import Definitions.Def_ChapterGravityProjector
import Mathlib


/-!
# Chapter — Diffeomorphisms and gravity: the temporal projector `Π = δ − χ = −v⊗v♭`

Source: `book.tex`, chapter *"Diffeomorphisms and gravity"*, §*"Classical
Hamiltonian"* (line ~8091).  Continuing the standing directive (mine the next
self-contained mathematical claim from `book.tex`) and building directly on
`ChapterGravityProjector` (Wave 69), we treat the **complementary temporal
projector**

`Π^a{}_b = δ^a{}_b − χ^a{}_b = −v^a v_b`,

i.e. `Π = δ − χ`, where `χ^a{}_b = δ^a{}_b + v^a v_b` is the spatial projector
onto `v^⊥`.  Relative to a globally defined **unit timelike vector** `v`
(`minkSq v = −1` in the mostly-plus Minkowski metric `η = diag(−1,1,1,1)`), the
pair `(χ, Π)` is the orthogonal split of spacetime into the spatial hyperplane
`v^⊥` and the `1`-dimensional time direction spanned by `v`.  This file records
the self-contained linear-algebra facts of that decomposition, reusing `metric`,
`lower`, `minkSq`, `spatialProj` from `ChapterGravityProjector`.

Formalized here (all under `minkSq v = -1`):

* `timeProj v` — the projector `Π^a{}_b = −v^a v_b`;
* `spatialProj_add_timeProj` — **completeness** `χ + Π = δ` (the identity split);
* `timeProj_idempotent` — `Π² = Π` (a genuine projector);
* `trace_timeProj` — `tr Π = 1` (rank `1`: the time direction);
* `timeProj_mulVec_self` — `Π v = v`: `v` is fixed, spanning the image of `Π`;
* `spatialProj_mul_timeProj` — `χ · Π = 0` (the two projectors are orthogonal);
* `timeProj_mul_spatialProj` — `Π · χ = 0`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterGravityTimeProj

open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

/-- The temporal projector `Π^a{}_b = −v^a v_b = δ^a{}_b − χ^a{}_b`, as a `4×4`
matrix acting on contravariant vectors. -/
noncomputable def timeProj (v : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun a b => -(v a * lower v b))

/-
**Completeness**: the spatial and temporal projectors sum to the identity,
`χ + Π = δ`.
-/


/-
`Π` is idempotent: `Π² = Π`, a genuine (rank-1) projector.
-/


/-
`Π` has trace `1`: it is a rank-`1` projector onto the time direction.
-/


/-
`Π` fixes the timelike vector `v`: `Π v = v`, so `v` spans the image of the
temporal projector.
-/


/-
The spatial and temporal projectors are orthogonal: `χ · Π = 0`.
-/


/-
The spatial and temporal projectors are orthogonal: `Π · χ = 0`.
-/


end BookProof.ChapterGravityTimeProj


