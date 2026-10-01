-- Prove2me | Definitions.Def_ChapterAtomicDecomposition
-- name    : ChapterAtomicDecomposition
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:41:35.03999+00:00
-- url     : https://prove2.me/theorems/f2782fdf-0466-490b-99fe-d1c570d95b57
-- title:
--   Chapter AtomicDecomposition
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAtomicDecomposition.lean`): generated def bundle for ChapterAtomicDecomposition. See BookProof/ChapterAtomicDecomposition.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAtomicDecomposition.lean

import Mathlib


/-!
# The atomic / continuous classification of a probability measure

`BookProof.ChapterSelectingEvents` proves that every probability measure on a
space with measurable singletons splits into a continuous (atomless) part and a
part carried by the countable set of atoms
(`exists_continuous_atomic_decomposition`).  The book's chapter *"Selecting
events is not rewriting the history of events"* uses that splitting to state von
Neumann's classification of abelian von Neumann algebras into **five** types
(`book.tex` lines 8789–8800):

`ℓ∞({1,…,n})`, `ℓ∞(ℕ)`, `L∞([0,1])`, `L∞([0,1] ∪ {1,…,n})`, `L∞([0,1] ∪ ℕ)`.

The full `*`-isomorphism classification is von Neumann's theorem and is not
formalized here.  What *is* formalized is its exact measure-theoretic skeleton,
which is what the book's argument actually uses:

* `atoms_countable` — the set of atoms is countable;
* `atomicPart_eq_sum_dirac` — the atomic part of `μ` is literally a countable
  sum of point masses `∑ₓ μ{x}·δₓ`;
* `noAtoms_continuousPart` — the complementary part is atomless;
* `eq_continuousPart_add_atomicPart` — `μ` is the sum of the two;
* `not_continuousPart_zero_and_atoms_empty` — a probability measure cannot have
  both parts trivial;
* HEADLINE `probability_measure_five_types` — consequently every probability
  measure falls into exactly one of **five** mutually exclusive classes, indexed
  by (continuous part present or not) × (atoms: none / finitely many / countably
  infinitely many), matching the five types of the book's list one for one.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open MeasureTheory

namespace BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The set of **atoms** of a measure: the points carrying positive mass. -/
def atoms (mu : Measure X) : Set X := {x | 0 < mu {x}}





/-- The **continuous part** of `mu`: its restriction to the complement of the atoms. -/
noncomputable def continuousPart (mu : Measure X) : Measure X := mu.restrict (atoms mu)ᶜ

/-- The **atomic part** of `mu`: its restriction to the set of atoms. -/
noncomputable def atomicPart (mu : Measure X) : Measure X := mu.restrict (atoms mu)













end BookProof.ChapterAtomicDecomposition


