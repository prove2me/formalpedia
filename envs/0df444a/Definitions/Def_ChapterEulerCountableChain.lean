-- Prove2me | Definitions.Def_ChapterEulerCountableChain
-- name    : ChapterEulerCountableChain
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:51:03.652265+00:00
-- url     : https://prove2.me/theorems/1ae95a8b-7a92-495c-b85a-0eb58a3838a7
-- title:
--   Chapter EulerCountableChain
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterEulerCountableChain.lean`): generated def bundle for ChapterEulerCountableChain. See BookProof/ChapterEulerCountableChain.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEulerCountableChain.lean

import Mathlib


/-!
# Chapter — Euler's formula for a generic phase-space (the countable conditional-probability chain)

Formalization of the *countable / infinite* stick-breaking probability
distribution of `book.tex`, chapter *"Wave-function collapse versus Euler's
formula"*, §*"Euler's formula for a generic phase-space"* (`book.tex`
lines ~3565–3640).

For a **countable (possibly infinite)** partition of the phase-space the book
parametrizes the wave-function recursively as `vₙ = cₙ·lₙ + sₙ·vₙ₊₁` with
`cₙ = cos θₙ`, `sₙ = sin θₙ` and, upon collapse, obtains the classical
conditional-probability recursion.  Writing `(n or above) = {k : k ≥ n}` it
records (Equation `eq:cond`) the probability distribution as a *product of
conditional probabilities*:

> `P(n) = (∏_{k=1}^{n-1} P((k+1 or above) | (k or above))) · P(n | (n or above))`,
>   where `P(n | (n or above)) = cₙ²`,
>   `P((n+1 or above) | (n or above)) = sₙ²`, and
>   `P(n | (n or above)) + P((n+1 or above) | (n or above)) = 1`,

and remarks that *"the recursion does not need to stop"* — the parametrization is
valid in infinite dimensions.

This module formalizes the self-contained mathematical core of that infinite
chain, *independent* of any Hilbert-space or angle structure.  Let
`c : ℕ → ℝ` be the sequence of conditional probabilities
`c n = P(n | (n or above)) ∈ [0,1]` (so `1 - c n = P((n+1 or above) | (n or
above))`).  Define the *tail weight* `T N = P(N or above) = ∏_{k<N} (1 - c k)`
and the *point mass* `P n = T n · c n`.  We prove:

* `stickTail_succ` — the recursion `T (N+1) = T N · (1 - c N)`.
* `partial_sum` — the exact telescoping identity `∑_{n<N} P(n) = 1 - T N`
  (equivalently `∑_{n<N} P(n) + P(N or above) = 1`, the book's normalization).
* `stickProb_nonneg` / `stickTail_nonneg` — the weights are genuine
  probabilities when `c n ∈ [0,1]`.
* **HEADLINE `stick_hasSum_one`** / `stick_tsum_one` — if the tail weight
  `T N → 0` (the recursion "reaches every state"), the point masses sum to
  exactly `1`: `∑' n, P(n) = 1`.

We also connect the abstract chain to the book's Euler angles: with
`c n = cos²(θ n)` (`condCos`), `1 - c n = sin²(θ n)` and the point mass is
`P(n) = (∏_{k<n} sin²(θ k)) · cos²(θ n)` (`stickProb_euler`), exactly the book's
`P(n) = (∏ s_k²) c_n²`.

This complements the *finite* `n`-state result of `ChapterEulerNState` (which
shows every finite distribution is reproduced) with the *infinite* / countable
case the book emphasizes, and the *single-step* density-matrix identity of
`ChapterEulerGenericDensity`.

All results are `sorry`-free and `axiom`-clean (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators
open Filter Topology

namespace BookProof.ChapterEulerCountableChain

/-- The **tail weight** `T N = P(N or above) = ∏_{k<N} (1 - c k)`, where
`c k = P(k | (k or above))` is the `k`-th conditional probability. -/
def stickTail (c : ℕ → ℝ) (N : ℕ) : ℝ := ∏ k ∈ Finset.range N, (1 - c k)

/-- The **point mass** `P n = T n · c n = P(n or above) · P(n | (n or above))`,
the probability of outcome `n` in the book's chain. -/
def stickProb (c : ℕ → ℝ) (n : ℕ) : ℝ := stickTail c n * c n

















/-! ## Connection to the book's Euler angles

With the conditional probabilities `c n = cos²(θ n)` the tail weights become
products of `sin²`, recovering the book's `P(n) = (∏_{k<n} s_k²) · c_n²`. -/

/-- The Euler conditional probability `c n = cos²(θ n) = P(n | (n or above))`. -/
noncomputable def condCos (θ : ℕ → ℝ) (n : ℕ) : ℝ := Real.cos (θ n) ^ 2









end BookProof.ChapterEulerCountableChain


