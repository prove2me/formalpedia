-- Prove2me | Definitions.Def_ChapterCompactCompleteReducibility
-- name    : ChapterCompactCompleteReducibility
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:35:26.732822+00:00
-- url     : https://prove2.me/theorems/2106e701-22ee-4b85-92c9-668f4189f312
-- title:
--   Chapter CompactCompleteReducibility
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCompactCompleteReducibility.lean`): generated def bundle for ChapterCompactCompleteReducibility. See BookProof/ChapterCompactCompleteReducibility.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCompactCompleteReducibility.lean

import Mathlib


/-!
# Weyl's unitarian trick for a compact group: complete reducibility by Haar averaging

Source: `book.tex`, chapter *"Real representations, CPT theorem and the relativistic position
operator"*, **Note 23** (Weyl): *finite-dimensional representations are completely reducible*.
The manuscript quotes the theorem as an external input, and in the development it is carried
as the named hypothesis `BookProof.ChapterA3w.WeylCompleteReducibility`.

Two special cases are already theorems in this development:

* `BookProof.ChapterUnitaryCompleteReducibility` — for a **unitary** representation of an
  arbitrary group (the orthogonal complement of an invariant subspace is invariant);
* `BookProof.ChapterMaschkeFiniteGroup` — for a **finite** group (Maschke's averaging).

This file proves the remaining classical case, the one Weyl's *unitarian trick* is named for:
a **compact** group, where the finite average of Maschke's argument is replaced by the Haar
integral.  No inner product is assumed on the representation space and the group is arbitrary
compact (in particular `SU(N)`, the gauge groups of the book's field-theory chapters).

## Results

* `avgOp` — the Haar average `p = ∫_G ρ(g) ∘ T ∘ ρ(g)⁻¹ dg` of an arbitrary continuous
  projection `T` onto the invariant subspace `W`;
* `avgOp_apply_mem`, `avgOp_apply_eq_self` — `p` still maps into `W` and is the identity on
  `W`, so it is again a projection onto `W`;
* **`avgOp_comm`** — `p` commutes with the representation, which is what the averaging is
  for;
* **`compact_invariant_complement`** — hence every invariant subspace of a
  finite-dimensional continuous representation of a compact group has an **invariant
  complement**: the kernel of `p`.  This is the shape assumed by
  `ChapterA3w.WeylCompleteReducibility`, here proved for compact groups;
* `compact_invariant_complement_haar` — the same with no measure to choose: the normalized
  Haar measure of the compact group does the averaging.

Everything is `sorry`-free and uses only the standard axioms; no `EXTERNAL` hypothesis and no
`axiom` is introduced.
-/

namespace BookProof.ChapterCompactCompleteReducibility

open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The conjugate `ρ(g) ∘ T ∘ ρ(g)⁻¹` of an operator by the representation. -/
noncomputable def conjOp (ρ : G →* (V ≃L[ℂ] V)) (T : V →L[ℂ] V) (g : G) : V →L[ℂ] V :=
  ((ρ g : V →L[ℂ] V).comp (T.comp ((ρ g).symm : V →L[ℂ] V)))





/-- **The Haar average of a projection.** -/
noncomputable def avgOp (μ : Measure G) (ρ : G →* (V ≃L[ℂ] V)) (T : V →L[ℂ] V) : V →L[ℂ] V :=
  ∫ g, conjOp ρ T g ∂μ











/-- The normalized Haar measure of a compact Hausdorff group is a probability measure. -/
instance isProbabilityMeasure_haarMeasure_top [T2Space G] :
    IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) := by
  constructor
  simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G))



end BookProof.ChapterCompactCompleteReducibility


