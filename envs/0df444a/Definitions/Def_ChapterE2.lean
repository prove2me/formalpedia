-- Prove2me | Definitions.Def_ChapterE2
-- name    : ChapterE2
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:44:39.521369+00:00
-- url     : https://prove2.me/theorems/01c61965-6d80-43da-8140-13cd328cfa46
-- title:
--   Chapter E2
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterE2.lean`): generated def bundle for ChapterE2. See BookProof/ChapterE2.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterE2.lean

import Mathlib


/-!
# Chapter E (continued) — Euler's formula for a generic phase-space

This file formalizes the mathematical content of the `book.tex` sections
*"Euler's formula for a phase-space with 4 states"* and *"Euler's formula for a
generic phase-space"* (Chapter *"Wave-function collapse versus Euler's formula"*,
`book.tex` line ~3565), extending `BookProof/ChapterE.lean` (which handled the
2-state clock).

The book parametrizes a real normalized wave-function of an `n`-state (or
countable) phase-space by *Euler angles* `θ₁, θ₂, …` via the recursion
`vₙ = cos(θₙ) lₙ + sin(θₙ) vₙ₊₁`, and observes that the resulting Born
probabilities are

```
P(1) = c₁²,   P(2) = (s₁ c₂)²,   P(3) = (s₁ s₂ c₃)²,   …
```

i.e. a *stick-breaking* construction with conditional "stop-here" probability
`cₖ² = cos²(θₖ)` and conditional "go-higher" probability `sₖ² = sin²(θₖ)`.  The
book's point is twofold:

* these are a genuine probability distribution (they are nonnegative and sum to
  `1`), and
* **every** probability distribution on `n` states is realized this way (the
  conditional probabilities `cos²(θₖ)` are arbitrary, so the distribution is
  arbitrary) — "any probability distribution can be reproduced by the Born rule
  for some wave-function".

We model the angles by a function `θ : ℕ → ℝ` (values outside the relevant range
are irrelevant), which avoids `Fin`-index arithmetic.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped BigOperators
open Finset

namespace BookProof.ChapterE2

/-- The Born probability of "stopping exactly at index `n`":
`(∏_{k<n} sin²θₖ) · cos²θₙ`. -/
noncomputable def stick (θ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ range n, Real.sin (θ k) ^ 2) * Real.cos (θ n) ^ 2

/-- The "`N` or above" remaining probability after `N` steps: `∏_{k<N} sin²θₖ`. -/
noncomputable def remainder (θ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ k ∈ range N, Real.sin (θ k) ^ 2

/-- The Born distribution of an `n`-state phase-space: stopping probabilities at
`0, …, n-2` and the remainder at the last index `n-1`. -/
noncomputable def bornProb (θ : ℕ → ℝ) (n : ℕ) (i : Fin n) : ℝ :=
  if (i : ℕ) + 1 < n then stick θ (i : ℕ) else remainder θ (i : ℕ)

/-! ## Basic identities -/













/-! ## Normalization (the telescoping identity) -/

/-
**Telescoping normalization.** The partial sum of the stopping probabilities
plus the remainder equals `1`.  (Because `stick θ N = remainder θ N · cos²θ_N`
and `remainder θ (N+1) = remainder θ N · sin²θ_N`, with `cos² + sin² = 1`.)
-/


/-! ## The Born family is a probability distribution -/



/-
**The Born distribution of an `n`-state phase-space sums to `1`.**
-/


/-! ## Arbitrariness: any distribution is realized by the Born rule -/



/-
**Headline (Euler's formula for a generic phase-space).** Every probability
distribution `p` on `n` states is realized by the Born rule of some
wave-function, i.e. there exist Euler angles `θ` whose stick-breaking Born
distribution `bornProb θ n` equals `p`.
-/


end BookProof.ChapterE2


