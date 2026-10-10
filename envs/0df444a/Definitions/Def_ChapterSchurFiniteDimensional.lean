-- Prove2me | Definitions.Def_ChapterSchurFiniteDimensional
-- name    : ChapterSchurFiniteDimensional
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T07:19:53.020806+00:00
-- url     : https://prove2.me/theorems/640f7f24-e077-485d-a916-e09a64accde8
-- title:
--   Chapter SchurFiniteDimensional
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSchurFiniteDimensional.lean`): generated def bundle for ChapterSchurFiniteDimensional. See BookProof/ChapterSchurFiniteDimensional.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchurFiniteDimensional.lean

import Definitions.Def_ChapterA2b
import Definitions.Def_ChapterA
import Mathlib


/-!
# Schur's lemma in finite dimension, and the real / pseudoreal dichotomy

Source: `book.tex`, chapter *"Real representations, CPT theorem and the relativistic
position operator"*, §"Finite-dimensional representations": **Lemma 20** (Schur's lemma for
finite-dimensional representations) and the core of **Lemma 21** (an anti-isomorphism of an
irreducible finite-dimensional complex system squares to a real scalar).

`BookProof.ChapterSchurIrreducible` proves Schur's lemma for a topologically irreducible
**normal** system on a complex Hilbert space (the hypothesis `Def 24` of the book), which is
what the infinite-dimensional chapters need.  In finite dimension the book states the lemma
with **no** normality hypothesis, and the proof is the eigenvalue argument rather than the
spectral one.  This file supplies that version, so that Props 17–19 of `ChapterA2b` and
`ChapterA2c` — whose hypotheses are `IsSchurFull` / `IsSchurUnitary` — apply to *every*
irreducible finite-dimensional complex system, normal or not.

## Results

* **`isSchurFull_of_irreducible_finiteDimensional` (Lemma 20)** — for an irreducible system
  on a nonzero finite-dimensional complex Hilbert space, every bounded operator commuting
  with the system is a complex scalar.  The proof: a commuting operator has an eigenvalue
  `c`, and `ker (S − c)` is a nonzero subsystem, hence everything.
* `isSchurUnitary_of_irreducible_finiteDimensional` — the unitary form of the same statement.
* **`antiUnitary_sq_of_irreducible_finiteDimensional` (Lemma 21, core)** — an anti-unitary
  commuting with such a system satisfies `θ² = 1` or `θ² = −1`: the real / pseudoreal
  dichotomy.  `θ²` is a commuting complex-linear isometry, hence a scalar `c` of modulus one
  by Lemma 20; conjugating `θ` past it forces `c` to be real.
* `isConjugation_or_sq_eq_neg_one` — the same statement in the book's vocabulary: either `θ`
  is a C-conjugation (`IsConjugation`, Def 8.1) of the system, or it is a pseudoreal
  structure `θ² = −1`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterSchurFiniteDimensional

open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ## Lemma 20 — Schur's lemma in finite dimension -/





/-! ## Lemma 21 — the square of a commuting anti-unitary -/

/-- The square of an anti-unitary, as a complex-linear bounded operator. -/
noncomputable def antiSq (θ : AntiUnitary V) : V →L[ℂ] V where
  toFun x := θ (θ x)
  map_add' x y := by simp
  map_smul' c x := by rw [map_smulₛₗ, map_smulₛₗ]; simp
  cont := θ.continuous.comp θ.continuous

omit [CompleteSpace V] in
@[simp] theorem antiSq_apply (θ : AntiUnitary V) (x : V) : antiSq θ x = θ (θ x) := rfl





/-! ## Payoff: Prop 17 with no Schur hypothesis in finite dimension -/



end BookProof.ChapterSchurFiniteDimensional


