-- Prove2me | Definitions.Def_ChapterSolovayTailDimension
-- name    : ChapterSolovayTailDimension
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T12:06:41.014828+00:00
-- url     : https://prove2.me/theorems/0b1434b5-70c2-4d66-aeba-abaa886aa401
-- title:
--   The Lean 4 theorem `substrateInterval_measurableSet` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSolovayTailDimension.lean`): generated def bundle for ChapterSolovayTailDimension. See BookProof/ChapterSolovayTailDimension.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSolovayTailDimension.lean

import Definitions.Def_PhysMehler
import Mathlib


/-!
# The Kopperman tail is infinite dimensional (plan §4.1, Task B2b)

`PhysMehler.substrate_orthonormal_pair` exhibits *two* orthonormal vectors in the
substrate `L²([0,1])` — the `√2`-scaled indicators of the two halves.  This module
generalizes that construction to a **countable** orthonormal family (the scaled
indicators of the disjoint intervals `(1/(n+2), 1/(n+1)]`) and concludes that the
substrate — hence the Kopperman tail `InnerTail` of the Solovay decomposition — is
not finite dimensional.

## Deliverables

* `substrateInterval` / `substrateIntervals_disjoint` — the disjoint intervals and
  their positive measures;
* `substrate_orthonormal_family` — a countable orthonormal family in the
  substrate;
* `substrate_infinite_dimensional` — `¬ FiniteDimensional ℝ Substrate`;
* `tail_infinite_dimensional` — **headline**: `¬ FiniteDimensional ℝ InnerTail`.
  The tail really does carry infinitely many independent directions, so the head /
  tail split of the Solovay decomposition is not a finite-dimensional artefact.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal

namespace BookProof.ChapterSolovayTailDimension

/-! ## A countable family of disjoint intervals in `[0,1]` -/

/-- The `n`-th interval of the countable partition of `(0,1]` used to build an
orthonormal family in the substrate: `(1/(n+2), 1/(n+1)]`. -/
def substrateInterval (n : ℕ) : Set ℝ := Ioc (1 / (n + 2) : ℝ) (1 / (n + 1) : ℝ)

theorem substrateInterval_measurableSet (n : ℕ) : MeasurableSet (substrateInterval n) :=
  measurableSet_Ioc





theorem substrateInterval_measure_ne_top (n : ℕ) : unitMeasure (substrateInterval n) ≠ ∞ :=
  measure_ne_top _ _





/-! ## A countable orthonormal family -/

/-- The `n`-th member of the orthonormal family: the indicator of
`substrateInterval n`, scaled to unit `L²` norm. -/
def substrateBasisVector (n : ℕ) : Substrate :=
  indicatorConstLp 2 (substrateInterval_measurableSet n) (substrateInterval_measure_ne_top n)
    (Real.sqrt (unitMeasure.real (substrateInterval n)))⁻¹







/-! ## The substrate, and hence the tail, is infinite dimensional -/





end BookProof.ChapterSolovayTailDimension

end


