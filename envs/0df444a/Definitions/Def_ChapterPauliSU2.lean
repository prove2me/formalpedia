-- Prove2me | Definitions.Def_ChapterPauliSU2
-- name    : ChapterPauliSU2
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:52:31.711907+00:00
-- url     : https://prove2.me/theorems/f5ee2182-00fe-49c4-938e-5ffe39f33b0f
-- title:
--   Chapter PauliSU2
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPauliSU2.lean`): generated def bundle for ChapterPauliSU2. See BookProof/ChapterPauliSU2.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPauliSU2.lean

import Definitions.Def_ChapterPauliLorentz
import Mathlib


/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"On the Lorentz, SL(2,C) and Pin(3,1) groups": the `SU(2) → SO(3)` restriction of
the spinor map

Source: `book.tex`, chapter *"Real representations, CPT theorem and the
relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1)
groups"*, **Note 47 / Def 49** (`book.tex` line ~5455): the spinor map
`Υ : SL(2,ℂ) → SO⁺(1,3)`, `Υᵘ_ν(T) σ^ν = T† σᵘ T`, restricts on the compact
subgroup `SU(2) = Spin⁺(3,1) ∩ SU(4)` to the **double cover of `SO(3)`**.

This file continues `ChapterPauliLorentz` with the self-contained algebraic
facts that make that restriction work, all at the level of concrete `2×2`
complex matrices (no gamma/Majorana matrices, no gravity, no spherical-Bessel
numerics):

- the spinor conjugation `X ↦ T† X T` is a (right) action: it is compatible with
  the group multiplication of `SL(2,ℂ)` and is **two-to-one** (`±T` act the same),
  which is the "double cover" mechanism;
- for a **unitary** `T` (`T† T = 1`, i.e. `T ∈ SU(2)` once `det T = 1`) the
  conjugation **preserves the trace** of the hermitian matrix, hence **fixes the
  time component** `x⁰` of the 4-vector;
- combined with the Minkowski-form preservation from `ChapterPauliLorentz`
  (`spinorMap_preserves_mink`), an `SU(2)` element therefore **preserves the
  Euclidean length of the spatial part** `(x¹)² + (x²)² + (x³)²`: it induces a
  rotation in `SO(3)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix
open scoped BigOperators

namespace BookProof.ChapterPauliSU2

open BookProof.ChapterPauliLorentz

/-! ## The spinor conjugation as a two-to-one right action -/

/-- The spinor conjugation `X ↦ T† X T`. -/
noncomputable def spinorAction (T X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := Tᴴ * X * T

/-
The spinor conjugation is compatible with group multiplication: conjugating by
`T₁ * T₂` is the same as conjugating first by `T₁` and then by `T₂` (a right
action of the group).
-/


/-
**Two-to-one:** `T` and `-T` induce the same spinor conjugation.  This is the
`±1` kernel that makes `Υ : SL(2,ℂ) → SO⁺(1,3)` a double cover.
-/


/-
The spinor conjugation preserves hermiticity.
-/


/-! ## The unitary case: `SU(2)` fixes the time component -/

/-
For a **unitary** `T` (`T† T = 1`), the spinor conjugation preserves the trace
of any matrix.  (In the physics dictionary `x⁰ = ½ tr(X)`, so a unitary `T`
fixes the time component of the 4-vector.)
-/


/-
For a unitary `T`, the spinor conjugation **fixes the time component** `x⁰` of
the 4-vector: `y⁰ = x⁰` where `T† (xᵤσᵘ) T = yᵤσᵘ`.
-/


/-! ## The headline: `SU(2)` preserves the Euclidean spatial length -/

/-- The squared Euclidean length of the spatial part of a 4-vector. -/
def spatialNormSq (x : Fin 4 → ℝ) : ℝ := (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2

/-
**Headline (the `SU(2) → SO(3)` restriction).**  For `T ∈ SU(2)`
(`T† T = 1` and `det T = 1`), the spinor conjugation `X ↦ T† X T` preserves the
Euclidean length of the spatial part of the 4-vector: with `T† (xᵤσᵘ) T = yᵤσᵘ`,
we have `(y¹)² + (y²)² + (y³)² = (x¹)² + (x²)² + (x³)²`.  Together with the fact
that it fixes `x⁰` (`su2_preserves_time`), this says the induced map is a spatial
rotation in `SO(3)`.
-/


end BookProof.ChapterPauliSU2


