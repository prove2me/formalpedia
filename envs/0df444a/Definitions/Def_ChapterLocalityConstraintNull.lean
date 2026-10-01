-- Prove2me | Definitions.Def_ChapterLocalityConstraintNull
-- name    : ChapterLocalityConstraintNull
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:18:54.310874+00:00
-- url     : https://prove2.me/theorems/5b9a1c1c-60d1-4c8e-a97e-6479e682c622
-- title:
--   Chapter LocalityConstraintNull
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLocalityConstraintNull.lean`): generated def bundle for ChapterLocalityConstraintNull. See BookProof/ChapterLocalityConstraintNull.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLocalityConstraintNull.lean

import Mathlib


/-!
# The local velocity constraint has null measure

Source: `book.tex`, chapter *"Gauge symmetry and dissipative dynamics in probability
spaces"*, §*"Balancing discretization and locality"* (`book.tex` line ~2487), closing
paragraph:

> *"The main difficulty lies in defining a probability measure when the velocity is
> constrained by the position at each time, since the subset defined by the constraints
> has null measure when considering the Gaussian measure for the position and
> (unconstrained) velocity."*

This file proves that statement, in the generality in which it is used: the *constraint
set* is the graph

```
graphSet f = { (x, v) | v = f x }
```

of the map `f` expressing the constrained variable (the velocity) in terms of the free one
(the position), and the claim is that it is a null set for **every** product measure whose
second factor is atomless — in particular for a Gaussian law on the unconstrained velocity,
and for the two-dimensional Lebesgue measure.

The mechanism is Fubini: every vertical section of the graph is the single point `f x`, and
an atomless measure gives no mass to a point.  The consequence the chapter draws is also
recorded: the naive conditioning of the joint law on the constraint is not a probability
measure — the restricted measure is identically zero (`restrict_graphSet_eq_zero`), so a
coherent "uncertainty after the constraint" must be built differently (which is what the
wave-function parametrization of the other chapters does).

## Main results

* `graphSet_null` — the constraint set is null for `μ.prod ν` whenever `ν` is atomless.
* `graphSet_volume_null` — the two-dimensional Lebesgue special case.
* `graphSet_gaussian_null` — the Gaussian special case stated in the book.
* `restrict_graphSet_eq_zero`, `not_isProbabilityMeasure_restrict_graphSet` — conditioning
  the joint law on the constraint yields the zero measure, not a probability measure.
-/

namespace BookProof.LocalityConstraint

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

/-- The constraint set: the graph of the map `f` giving the constrained variable (the
velocity) as a function of the free variable (the position). -/
def graphSet (f : α → ℝ) : Set (α × ℝ) := {p : α × ℝ | p.2 = f p.1}















end BookProof.LocalityConstraint


