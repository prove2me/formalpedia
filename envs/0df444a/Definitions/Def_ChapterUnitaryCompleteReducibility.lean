-- Prove2me | Definitions.Def_ChapterUnitaryCompleteReducibility
-- name    : ChapterUnitaryCompleteReducibility
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:01:56.754987+00:00
-- url     : https://prove2.me/theorems/f92a2953-3d21-4914-b9d3-779de5e3c46c
-- title:
--   Chapter UnitaryCompleteReducibility
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterUnitaryCompleteReducibility.lean`): generated def bundle for ChapterUnitaryCompleteReducibility. See BookProof/ChapterUnitaryCompleteReducibility.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnitaryCompleteReducibility.lean

import Mathlib


/-!
# The unitarian trick: complete reducibility of unitary representations

`BookProof.ChapterA3w` takes **Weyl's complete-reducibility theorem** as an
`EXTERNAL` named hypothesis, because for the *non-compact* group `SL(2,ℂ)` it is
genuinely unavailable in Mathlib.  For **unitary** representations the theorem is
elementary — it is Weyl's *unitarian trick* — and this file proves it outright,
with no external input:

* `orthogonal_isInvariant` — the orthogonal complement of an invariant subspace
  of a unitary representation is invariant (valid in any complex inner-product
  space, any group);
* `unitary_complete_reducibility` — in finite dimensions every invariant subspace
  therefore has an invariant complement, namely its orthogonal complement;
* `exists_irreducible_invariant_le` — every nonzero invariant subspace contains an
  irreducible one (a minimal nonzero invariant subspace);
* `exists_irreducible_decomposition` — every invariant subspace is the join of a
  finite list of irreducible invariant subspaces, so a finite-dimensional unitary
  representation is a sum of irreducibles.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterUnitaryCompleteReducibility

open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A subspace `W` is **invariant** under the unitary representation `ρ` iff every
`ρ g` maps `W` into itself. -/
def IsInvariant (ρ : G →* (V ≃ₗᵢ[ℂ] V)) (W : Submodule ℂ V) : Prop :=
  ∀ g : G, ∀ x ∈ W, ρ g x ∈ W

/-- An invariant subspace is **irreducible** iff it is nonzero and its only
invariant subspaces are `⊥` and itself. -/
def IsIrreducibleInvariant (ρ : G →* (V ≃ₗᵢ[ℂ] V)) (W : Submodule ℂ V) : Prop :=
  IsInvariant ρ W ∧ W ≠ ⊥ ∧ ∀ U ≤ W, IsInvariant ρ U → U = ⊥ ∨ U = W















end BookProof.ChapterUnitaryCompleteReducibility


