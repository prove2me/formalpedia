-- Prove2me | Definitions.Def_ChapterGravitySplit
-- name    : ChapterGravitySplit
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:19:17.530448+00:00
-- url     : https://prove2.me/theorems/fc45267e-1175-461a-9079-75839f7094c2
-- title:
--   Chapter GravitySplit
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGravitySplit.lean`): generated def bundle for ChapterGravitySplit. See BookProof/ChapterGravitySplit.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGravitySplit.lean

import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
import Mathlib


/-!
# Chapter — Diffeomorphisms and gravity: the orthogonal spacetime split `x = χx + Πx`

Source: `book.tex`, chapter *"Diffeomorphisms and gravity"*, §*"Classical
Hamiltonian"* (line ~8091).  Continuing the standing directive (mine the next
self-contained mathematical claim from `book.tex`) and building directly on the
spatial projector `χ` (`ChapterGravityProjector`, Wave 69) and the complementary
temporal projector `Π` (`ChapterGravityTimeProj`, Wave 71), this file records the
**orthogonal `3 + 1` decomposition** that these projectors implement: relative to
the globally defined **unit timelike vector** `v` (`minkSq v = −1` in the
mostly-plus Minkowski metric `η = diag(−1,1,1,1)`), every contravariant vector
`x` splits uniquely as

`x = (χ x) + (Π x)`,

into its **spatial part** `χ x ∈ v^⊥` and its **temporal part** `Π x`, which is a
scalar multiple of `v`.  The two parts are Minkowski-orthogonal.  This is the
linear-algebra content underlying the book's use of `χ` to split every torsion
tensor into spatial and temporal pieces.

Formalized here (all under the physical unit-timelike hypothesis
`minkSq v = -1`, where noted):

* `minkForm x y` — the Minkowski bilinear form `⟨x,y⟩_η = ∑ₐ xᵃ y_a`;
* `minkForm_comm` — the Minkowski form is symmetric;
* `spatialPart v x`, `timePart v x` — the spatial (`χx`) and temporal (`Πx`) parts;
* `spatialPart_add_timePart` — **completeness** `χx + Πx = x`;
* `timePart_eq_smul` — the temporal part is `Πx = −⟨x,v⟩_η · v`, a multiple of `v`;
* `spatialPart_orthogonal` — the spatial part is Minkowski-orthogonal to `v`
  (`⟨χx, v⟩_η = 0`), i.e. it lies in the spatial hyperplane `v^⊥`;
* `parts_orthogonal` — **headline**: the spatial and temporal parts are
  Minkowski-orthogonal (`⟨χx, Πx⟩_η = 0`);
* `split_unique` — the `3 + 1` split is unique: if `x = s + c • v` with `s ⊥ v`
  then `s = χx` and `c • v = Πx`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterGravitySplit

open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

/-- The Minkowski bilinear form `⟨x,y⟩_η = ∑ₐ xᵃ y_a = ∑ₐ xᵃ η_{ab} yᵇ`. -/
noncomputable def minkForm (x y : Fin 4 → ℝ) : ℝ := ∑ a, x a * lower y a

/-
The Minkowski form is symmetric.
-/


/-
`minkForm x x` is the Minkowski square `minkSq x`.
-/


/-- The **spatial part** `χ x` of a vector `x`. -/
noncomputable def spatialPart (v x : Fin 4 → ℝ) : Fin 4 → ℝ := (spatialProj v).mulVec x

/-- The **temporal part** `Π x` of a vector `x`. -/
noncomputable def timePart (v x : Fin 4 → ℝ) : Fin 4 → ℝ := (timeProj v).mulVec x

/-
**Completeness.** The spatial and temporal parts reconstruct `x`: `χx + Πx = x`.
-/


/-
The temporal part is a scalar multiple of `v`: `Πx = −⟨x,v⟩_η · v`.
-/


/-
The spatial part is Minkowski-orthogonal to `v` (`⟨χx, v⟩_η = 0`): it lies in the
spatial hyperplane `v^⊥`.
-/


/-
**Headline.** The spatial and temporal parts are Minkowski-orthogonal:
`⟨χx, Πx⟩_η = 0`.
-/


/-
**Uniqueness of the `3 + 1` split.** If `x = s + c • v` with `s` Minkowski-orthogonal
to `v` (`⟨s, v⟩_η = 0`), then `s` is the spatial part and `c • v` is the temporal
part.
-/


end BookProof.ChapterGravitySplit


