-- Prove2me | Definitions.Def_ChapterF6
-- name    : ChapterF6
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:55:05.288904+00:00
-- url     : https://prove2.me/theorems/5ec17212-da45-4108-9863-c12f04e40529
-- title:
--   Chapter F6
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterF6.lean`): generated def bundle for ChapterF6. See BookProof/ChapterF6.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterF6.lean

import Mathlib


/-!
# Chapter F6 — Quantum Flow Matching: the Misra–Gries heavy-hitter bound (roadmap N14, F3.5, §8
Phase 4)

This file formalizes the **Misra–Gries** frequency-estimation guarantee used in
the QFM tomographic-recovery pipeline (source `RiemannProof/QFM.tex` §8 Phase 4;
reference implementation `../unfer/qfm/`).  With a table of at most `k` counters,
the Misra–Gries summary of a stream `s` produces, for every item `x`, a frequency
estimate `f̂(x) = (mg k s) x` satisfying

  `f(x) − N/k ≤ f̂(x) ≤ f(x)`,

where `f(x) = s.count x` is the true frequency and `N = s.length` the stream
length.  This is the top-1 peak-recovery guarantee: the estimate never
overshoots and undershoots by at most `N/k`.

## Model

The counter table is a finitely-supported map `T : α →₀ ℕ`.  Processing one item
`x` with capacity `k`:

* if `x` is already counted (`0 < T x`) or there is a free slot
  (`T.support.card < k`), increment `x`'s counter (`T + single x 1`);
* otherwise (`x` absent and the table full) **decrement every counter by one**
  (`T.mapRange (· - 1)`), which drops any counter that hits `0`.

`mgD k T s` counts the number of decrement rounds along the run.

## Deliverables

* `mg_upper` — the estimate never overshoots: `(mg k s) x ≤ s.count x`.
* `mg_lower` — the estimate undershoots by at most the decrement count:
  `s.count x ≤ (mg k s) x + mgD k 0 s`.
* `mgD_bound` — the decrement count is small: `k * mgD k 0 s ≤ s.length`.
* `misra_gries_bound` — the headline `f(x) − N/k ≤ f̂(x) ≤ f(x)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis**.
-/

open scoped BigOperators

namespace BookProof.ChapterF6

variable {α : Type*} [DecidableEq α]

/-- One Misra–Gries step with capacity `k`: increment if the item is present or
there is a free slot, else decrement every counter by one. -/
noncomputable def mgStep (k : ℕ) (T : α →₀ ℕ) (x : α) : α →₀ ℕ :=
  if 0 < T x ∨ T.support.card < k then
    T + Finsupp.single x 1
  else
    T.mapRange (fun n => n - 1) (by norm_num)

/-- The Misra–Gries table obtained by folding `mgStep` over the stream from an
initial table `T`. -/
noncomputable def mgT (k : ℕ) (T : α →₀ ℕ) (s : List α) : α →₀ ℕ :=
  s.foldl (mgStep k) T

/-- The number of decrement rounds along a Misra–Gries run. -/
noncomputable def mgD (k : ℕ) : (α →₀ ℕ) → List α → ℕ
  | _, [] => 0
  | T, x :: xs => (if 0 < T x ∨ T.support.card < k then 0 else 1) + mgD k (mgStep k T x) xs

/-- The Misra–Gries summary of a stream `s` with capacity `k` (empty initial
table). -/
noncomputable def mg (k : ℕ) (s : List α) : α →₀ ℕ := mgT k 0 s

/-- The total mass stored in a table. -/
noncomputable def mgSum (T : α →₀ ℕ) : ℕ := T.sum (fun _ n => n)









/-! ### Per-step facts -/



/-
One step increments the counter of `x` by at most one and never changes any
other counter by more than the indicator of `x`.
-/


/-
Per-step lower bound: the counter of `y` plus the occurrence indicator is at
most the new counter plus the decrement indicator.
-/


/-! ### The capacity invariant -/



/-! ### Upper bound -/

/-
Upper bound (general initial table): the estimate is at most the initial
value plus the number of occurrences.
-/




/-! ### Lower bound -/

/-
Lower bound (general initial table): the true count plus initial value is at
most the estimate plus the number of decrement rounds.
-/




/-! ### The decrement count is small -/





 





/-! ### The headline bound -/

/-
**Misra–Gries heavy-hitter bound** (F3.5): with capacity `k ≥ 1`, the
frequency estimate satisfies `f(x) − N/k ≤ f̂(x) ≤ f(x)`, where `f(x) = s.count x`
and `N = s.length`.
-/


end BookProof.ChapterF6


