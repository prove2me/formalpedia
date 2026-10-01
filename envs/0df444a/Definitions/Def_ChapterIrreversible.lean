-- Prove2me | Definitions.Def_ChapterIrreversible
-- name    : ChapterIrreversible
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:04:58.884792+00:00
-- url     : https://prove2.me/theorems/153c8caf-6ee1-4e2e-987d-82fd8d542127
-- title:
--   Chapter Irreversible
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterIrreversible.lean`): generated def bundle for ChapterIrreversible. See BookProof/ChapterIrreversible.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterIrreversible.lean

import Mathlib


/-!
# Chapter "Reconstructing the classical trajectory of any isolated quantum system"
— §"Symmetries as irreversible processes"

Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any
isolated quantum system"*, subsection *"Symmetries as irreversible processes"*
(line ~2679).

The book argues: *"A non-deterministic symmetry transformation, when acting on a
deterministic ensemble increases the entropy of the ensemble after the
wave-function collapse and therefore must be an irreversible transformation."*
Conversely, if the symmetry is deterministic then the ensemble stays a
deterministic ensemble and the entropy is preserved (equal to `0`), so the
transformation is reversible. This is the entropy counterpart of the main
result of the chapter (*"time translation is a stochastic process if and only
if it is deterministic"*).

This file formalizes the self-contained information-theoretic core of that claim.

* A *deterministic ensemble* is a point mass (`IsPointMass`): the state of the
  system is known, so the probability vector is concentrated on one outcome.
* Acting with a Wigner symmetry `U` and collapsing the wave-function turns the
  initial basis state `e_k` into the **Born distribution** `bornDist v`, where
  `v = U e_k` is the corresponding column: `p_a = ‖v a‖²`.
* `entropy` is the Shannon entropy `∑_a negMulLog (p a) = ∑_a -p a · log (p a)`.

Headlines:

* `entropy_pointMass_zero` — a deterministic ensemble has entropy `0`.
* `entropy_nonneg` — the entropy of any probability vector is `≥ 0`.
* `entropy_pos_of_not_pointMass` — a non-deterministic ensemble has entropy `> 0`.
* `entropy_eq_zero_iff_pointMass` — entropy `0` **iff** deterministic ensemble.
* `entropy_bornDist_eq_zero_iff` — for a unit column `v`, the collapsed ensemble
  has entropy `0` **iff** `v` is a *deterministic column* (the symmetry maps the
  deterministic ensemble to a deterministic ensemble): the *reversible* case.
* `entropy_bornDist_pos_iff` — for a unit column `v`, the collapsed ensemble has
  entropy `> 0` **iff** `v` is *not* a deterministic column: the symmetry
  strictly increases the entropy — the *irreversible* case.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

open scoped BigOperators
open Finset

namespace BookProof.ChapterIrreversible

variable {n : ℕ}

/-- Shannon entropy of a finite probability vector `p : Fin n → ℝ`,
`H(p) = ∑_a -p a · log (p a)`. -/
noncomputable def entropy (p : Fin n → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

/-- A probability vector is a *deterministic ensemble* (point mass) when it is
concentrated on a single outcome. -/
def IsPointMass (p : Fin n → ℝ) : Prop :=
  ∃ a, p a = 1 ∧ ∀ b, b ≠ a → p b = 0

/-- The Born distribution obtained from a wave-function column `v` after
wave-function collapse: `p_a = ‖v a‖²`. -/
noncomputable def bornDist (v : Fin n → ℂ) : Fin n → ℝ :=
  fun a => ‖v a‖ ^ 2

/-- A wave-function column is a *deterministic column* when it is supported on a
single basis vector (the symmetry sends a basis state to a basis state up to a
phase). -/
def IsDeterministicColumn (v : Fin n → ℂ) : Prop :=
  ∃ a, v a ≠ 0 ∧ ∀ b, b ≠ a → v b = 0

/-
Each coordinate of the Born distribution is nonnegative.
-/


/-
The Born distribution of a unit column sums to `1`.
-/


/-
In a probability vector (nonnegative, summing to `1`), each coordinate is
`≤ 1`.
-/


/-
A deterministic ensemble has zero entropy.
-/


/-
The entropy of any probability vector is nonnegative.
-/


/-
A probability vector that is **not** a deterministic ensemble has some
coordinate strictly between `0` and `1`.
-/


/-
A non-deterministic ensemble has strictly positive entropy: a symmetry that
turns a deterministic ensemble into a non-deterministic one strictly increases
the entropy.
-/


/-
**Reversible iff deterministic (entropy form).** For a probability vector,
the entropy is `0` if and only if the ensemble is deterministic.
-/


/-
For a unit column, the collapsed Born ensemble is deterministic (a point
mass) if and only if the column itself is deterministic.
-/


/-
**Reversible case.** For a unit column `v`, the collapsed ensemble has
entropy `0` — the symmetry preserves the entropy of the deterministic ensemble —
if and only if `v` is a deterministic column.
-/


/-
**Irreversible case.** For a unit column `v`, the collapsed ensemble has
strictly positive entropy — the symmetry strictly increases the entropy of the
deterministic ensemble — if and only if `v` is **not** a deterministic column.
-/


end BookProof.ChapterIrreversible


