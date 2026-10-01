-- Prove2me | Definitions.Def_ChapterLocalOperators
-- name    : ChapterLocalOperators
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:07:14.050728+00:00
-- url     : https://prove2.me/theorems/11bb79c2-772d-470b-85ed-33bf8804642a
-- title:
--   Chapter LocalOperators
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLocalOperators.lean`): generated def bundle for ChapterLocalOperators. See BookProof/ChapterLocalOperators.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLocalOperators.lean

import Mathlib


/-!
# Chapter "Free field parametrization in Classical Statistical Field Theory and
Navier-Stokes equations" — §"Local operators and the momentum constraint"

Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical
Field Theory and Navier-Stokes equations"*, section *"Local operators and the
momentum constraint"* (line ~4011).

The book argues that, once the momentum constraint is imposed, **all operators
must be invariant under a translation in space**, so that *"in rigor we can't"*
define local operators.  What one *can* do is use translation-invariant
combinations of local operators, e.g. the space integral `∫ d\vec{x}\ l(\vec{x})`
of a local operator `l(\vec{x})`, which "behaves effectively as a local operator
when the wave-function is concentrated around one point".

This file formalizes the two self-contained mathematical claims underlying that
passage, for an operator-valued field on `d`-dimensional position space
`ℝ^d = Fin d → ℝ` with values in an arbitrary real Banach space `E` (the algebra
of operators):

* `localIntegral_translation_invariant` — the space integral `∫ l(x) dx` **is**
  translation invariant: shifting the local field `l` by any spatial vector `y`
  leaves the integral unchanged (`∫ l(x + y) dx = ∫ l(x) dx`).  This is the sense
  in which the translation-invariant operator `∫ d\vec{x}\ l(\vec{x})` is an
  admissible operator.
* `not_translationInvariant_of_pointSupported` — conversely, a genuinely *local*
  operator field (nonzero at a single point `x₀` and vanishing elsewhere) is
  **not** translation invariant (in dimension `d ≥ 1`); this is the precise sense
  in which local operators cannot be defined as admissible (translation-invariant)
  operators "in rigor".

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.LocalOperators

open MeasureTheory

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A *local operator field* on `d`-dimensional space is a map assigning to each
point `x ∈ ℝ^d` an operator `l x ∈ E`. -/
abbrev LocalField (d : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (Fin d → ℝ) → E

/-- The translation-invariant operator `∫ d\vec{x}\ l(\vec{x})` obtained by
integrating a local operator field over all of space. -/
noncomputable def localIntegral (l : LocalField d E) : E := ∫ x, l x

/-- `x` is *translation invariant* if shifting its argument by any spatial vector
leaves it unchanged.  Under the momentum constraint, only such operator fields are
admissible. -/
def TranslationInvariant (l : LocalField d E) : Prop :=
  ∀ y, (fun x => l (x + y)) = l







end BookProof.LocalOperators


