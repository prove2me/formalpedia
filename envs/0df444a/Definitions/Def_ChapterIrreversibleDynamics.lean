-- Prove2me | Definitions.Def_ChapterIrreversibleDynamics
-- name    : ChapterIrreversibleDynamics
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:13:31.563422+00:00
-- url     : https://prove2.me/theorems/d122bb60-251e-4087-b498-b7f9238a9b19
-- title:
--   Chapter IrreversibleDynamics
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterIrreversibleDynamics.lean`): generated def bundle for ChapterIrreversibleDynamics. See BookProof/ChapterIrreversibleDynamics.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterIrreversibleDynamics.lean

import Mathlib


/-!
# Chapter "Entropy and an irreversible deterministic time-evolution coexist",
§"Irreversible deterministic time-evolution" — irreversibility as an injective,
non-surjective, non-singular self-map.

Source: `book.tex`, chapter *"Entropy and an irreversible deterministic
time-evolution coexist"*, §*"Irreversible deterministic time-evolution"*
(line ~9524).

The book argues:

> *"A process with a dissipative time-evolution is irreversible: the
> deterministic time-evolution is not an invertible function (it is injective
> but not surjective). Then there is time asymmetry."*

and, just above, that the random discrete map *"almost surely maps sets of
non-null measure into sets of non-null measure (that is, it is non-singular)"*.

This module formalizes the self-contained mathematical core of these statements.

## The finite/discrete world admits no irreversible deterministic dynamics

On a **finite** state space (the `n²`-cell discrete world of the same section),
a deterministic self-map is injective iff surjective iff bijective. Hence there
is *no* injective-but-not-surjective self-map: a deterministic reversible/
irreversible dichotomy cannot appear. This is the discrete counterpart of the
book's remark that *"the rationals are not enough"* and *"a mixed standard
probability space ... is unavoidable"*.

* `finite_injective_iff_surjective`, `finite_injective_iff_bijective`.
* `finite_injective_imp_surjective` — an injective self-map of a finite type is
  automatically surjective (so it *is* invertible: reversible).
* `finite_no_irreversible` — there is no injective non-surjective self-map of a
  finite type.

## The continuum admits irreversible deterministic dynamics

On an **infinite** state space (the continuous limit) an injective,
non-surjective self-map exists — an irreversible deterministic time-evolution.

* `exists_injective_not_surjective` — a general Dedekind-infinite witness.
* `nat_succ_injective_not_surjective` — the concrete witness `n ↦ n+1` on `ℕ`.

## A concrete non-singular dissipative map on the unit interval

The book rescales to `[0,1]×[0,1]`. The map `dissipative x = x/2` is a concrete
*non-singular dissipative* deterministic time-evolution on `[0,1]`:

* `dissipative_injective` — it is injective.
* `dissipative_mapsTo_unitInterval` — it maps `[0,1]` into `[0,1]`.
* `dissipative_not_surjective_unitInterval` — but it is **not** onto `[0,1]`
  (`1` is not attained): irreversible.
* `dissipative_image_Icc` — its image of an interval `[a,b]` is `[a/2,b/2]`.
* `dissipative_volume_Icc` — the image has half the Lebesgue length: dissipative.
* `dissipative_nonsingular_Icc` — a positive-length interval is sent to a
  positive-measure set: it is **non-singular** (positive measure ↦ positive
  measure).
-/

namespace BookProof.IrreversibleDynamics

open MeasureTheory Function Set
open scoped ENNReal

/-! ### Finite discrete world: no irreversible deterministic dynamics -/









/-! ### Infinite (continuous-limit) world: irreversible dynamics exists -/





/-! ### A concrete non-singular dissipative map on the unit interval -/

/-- The dissipative time-evolution `x ↦ x/2` (rescaled to the book's unit
square). -/
noncomputable def dissipative : ℝ → ℝ := fun x => x / 2



















end BookProof.IrreversibleDynamics


