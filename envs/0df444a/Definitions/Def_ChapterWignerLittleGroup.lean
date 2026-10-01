-- Prove2me | Definitions.Def_ChapterWignerLittleGroup
-- name    : ChapterWignerLittleGroup
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:05:53.350255+00:00
-- url     : https://prove2.me/theorems/4538ff02-331e-4ded-a19b-d40f3cd58ca0
-- title:
--   Chapter WignerLittleGroup
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWignerLittleGroup.lean`): generated def bundle for ChapterWignerLittleGroup. See BookProof/ChapterWignerLittleGroup.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWignerLittleGroup.lean

import Mathlib


/-!
# Wigner's little-group classification (book.tex, Definition 78 / Proposition 79 and
§"Real unitary representations of the Poincaré group")

`BookProof.ChapterLittleGroup` formalizes the *abstract* content of Proposition 79 (the
coset description `H_k = G_l` of the little group) in an arbitrary group.  What the book
leaves as prose — and what `BookProof.ChapterA4h` still carries as the named hypothesis
`WignerClassification` — is the **concrete classification**: which momenta occur, which
subgroup of `SL(2,ℂ)` fixes each of them, and the fact that the little group only depends
on the orbit.  This file proves that classification.

## The model

We use the standard `SL(2,ℂ)` model of Minkowski space: a 4-momentum `p` is encoded by the
Hermitian matrix

  `hermOfMom p = !![p⁰+p³, p¹ - i p²; p¹ + i p², p⁰-p³]`,

so that `det (hermOfMom p) = p·p = (p⁰)² - |p⃗|²` (`hermOfMom_det`) and
`tr (hermOfMom p) = 2p⁰` (`hermOfMom_trace`).  `SL(2,ℂ)` acts by `A ⬝ X = A X A†`
(`act`), which preserves Hermiticity (`act_conjTranspose`) and the determinant, i.e. the
Minkowski square (`act_det`); this is the two-to-one covering `SL(2,ℂ) → SO⁺(1,3)`.
The **little group** of `p` (Definition 78 in this model) is the stabilizer

  `littleGroup p = {A | det A = 1 ∧ A (hermOfMom p) A† = hermOfMom p}`.

## Results

* `littleGroup_rest` — the little group of a massive rest momentum `(m,0,0,0)`, `m ≠ 0`,
  is exactly `SU(2) = {A | det A = 1 ∧ A A† = 1}`.
* `littleGroup_null` — the little group of the lightlike momentum `(1,0,0,1)` is exactly
  `{ !![a, b; 0, ā] : a ā = 1, b ∈ ℂ }`, the double cover `ℂ ⋊ U(1)` of the Euclidean
  group `SE(2)` of the plane; `nullElt_mul` is its semidirect-product multiplication law,
  `nullTranslations_*` exhibits the abelian translation subgroup `≅ (ℂ,+) ≅ ℝ²`, on which
  the rotation `a` acts by the *square* `a²` (`nullElt_conj_translation`) — the origin of
  half-integer helicity.
* `exists_boost_massive` / `exists_boost_null` — transitivity of the action on the
  massive future shell `p·p = m² > 0, p⁰ > 0` and on the future light cone
  `p·p = 0, p⁰ > 0, p ≠ 0`: every such `p` is `A·p₀A†` for an explicit `A ∈ SL(2,ℂ)`.
* `littleGroup_conj` — the little group of a transported momentum is the conjugate
  subgroup, so together with the two previous items: **every massive future momentum has
  little group conjugate to `SU(2)`, and every lightlike future momentum has little group
  conjugate to the `SE(2)` double cover** (`littleGroup_massive_conj_SU2`,
  `littleGroup_null_conj_SE2`).
* `mass_invariant` — the orbit invariant: the Minkowski square `p·p` is preserved by the
  action, so the massive shells, the light cone and the spacelike shells are unions of
  orbits (the second invariant, the sign of the energy, is not formalized here).

Everything is `sorry`-free and uses only the standard axioms.
-/

open Matrix Complex

namespace BookProof.ChapterWignerLittleGroup

/-! ## The Hermitian matrix of a 4-momentum -/

/-- The Hermitian `2×2` matrix `p⁰ + p⃗·σ⃗` attached to a 4-momentum `p`. -/
noncomputable def hermOfMom (p : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(p 0 : ℂ) + (p 3 : ℂ), (p 1 : ℂ) - I * (p 2 : ℂ);
     (p 1 : ℂ) + I * (p 2 : ℂ), (p 0 : ℂ) - (p 3 : ℂ)]







/-! ## The action of `SL(2,ℂ)` -/

/-- The action `A · X = A X A†` of `SL(2,ℂ)` on Hermitian matrices; under `hermOfMom`
this is the covering action of `SL(2,ℂ)` on Minkowski space. -/
noncomputable def act (A X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := A * X * Aᴴ















/-! ## The little group -/

/-- **Definition 78 in the `SL(2,ℂ)` model.** The little group of the momentum `p` is its
stabilizer in `SL(2,ℂ)`. -/
def littleGroup (p : Fin 4 → ℝ) : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {A | A.det = 1 ∧ act A (hermOfMom p) = hermOfMom p}

/-- `SU(2)`, the little group of a massive particle at rest. -/
def SU2 : Set (Matrix (Fin 2) (Fin 2) ℂ) := {A | A.det = 1 ∧ A * Aᴴ = 1}

/-- The double cover `ℂ ⋊ U(1)` of the Euclidean group `SE(2)`: the little group of a
lightlike momentum. -/
def SE2 : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {A | ∃ a b : ℂ, a * (starRingEnd ℂ) a = 1 ∧ A = !![a, b; 0, (starRingEnd ℂ) a]}

/-- The rest momentum `(m,0,0,0)`. -/
def restMom (m : ℝ) : Fin 4 → ℝ := ![m, 0, 0, 0]

/-- The reference lightlike momentum `(1,0,0,1)`. -/
def nullMom : Fin 4 → ℝ := ![1, 0, 0, 1]









/-! ### The semidirect structure of the null little group -/

/-- The generic element of the null little group: rotation `a` (with `a ā = 1`) and
translation `b`. -/
def nullElt (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; 0, (starRingEnd ℂ) a]









/-! ## Transitivity on the mass shells -/





/-! ## Conjugacy of little groups along an orbit -/







end BookProof.ChapterWignerLittleGroup


