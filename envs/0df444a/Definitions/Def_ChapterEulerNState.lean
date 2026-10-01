-- Prove2me | Definitions.Def_ChapterEulerNState
-- name    : ChapterEulerNState
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:53:53.02692+00:00
-- url     : https://prove2.me/theorems/c798dc2c-0dfa-40ca-98bc-8f6a646d64af
-- title:
--   Chapter EulerNState
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterEulerNState.lean`): generated def bundle for ChapterEulerNState. See BookProof/ChapterEulerNState.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEulerNState.lean

import Mathlib


/-!
# Chapter "Wave-function collapse versus Euler's formula", §§"Euler's formula for
a phase-space with 4 states" / "Euler's formula for a generic phase-space" — the
Born rule reproduces an arbitrary probability distribution

This file formalizes the self-contained mathematical claim of `book.tex`
(§"Euler's formula for a phase-space with 4 states", line ~3478, and its
generalization §"Euler's formula for a generic phase-space", line ~3565):

> *"any probability distribution for `n` states can be reproduced by the Born
> rule for some wave-function"*, via the Euler-angle (hyper-spherical /
> stick-breaking) parametrization
> `P(1) = c₁², P(2) = (s₁c₂)², P(3) = (s₁s₂c₃)², P(4) = (s₁s₂s₃)²`, where
> `cₙ = cos θₙ`, `sₙ = sin θₙ`, *"since for any probability `p` there is an angle
> `θₙ` such that `cₙ² = p`."*

This generalizes the 2-state result of `ChapterEulerStochastic` to `n` states.
We work with real coordinates in the book's orthonormal `l`-basis.

## Definitions

* `tailProd θ m` — the "remainder weight" `∏_{i<m} sin²(θ i)`
  (`= P(m or above)` in the book).
* `eulerWave θ n k` — the `k`-th real coordinate of the Euler wave-function
  `φ` for `n` states: `(∏_{i<k} sin θᵢ)·cos θₖ` for `k+1 < n`, and the
  cosine-free tail `∏_{i<k} sin θᵢ` for the last coordinate `k+1 = n`.
* `bornProb θ n k` — the Born probability `P(k) = |φₖ|²` of outcome `k`.

## Results

* `eulerWave_sq` — `bornProb = (eulerWave)²` (Born rule).
* `bornProb_nonneg` — every Born probability is `≥ 0`.
* `euler_sum_one` — **any** angles give a probability distribution:
  `∑_{k<n} bornProb θ n k = 1`.
* `euler_wave_unit` — the Euler wave-function is a unit vector.
* `euler_reproduces` — **headline**: for **any** probability distribution `p`
  on `{0,…,n-1}` there exist Euler angles `θ` whose Born probabilities equal
  `p`; i.e. every probability distribution is reproduced by the Born rule.
-/

open scoped BigOperators

namespace BookProof.ChapterEulerNState





/-- The remainder weight `∏_{i<m} sin²(θ i)` — the book's `P(m or above)`. -/
noncomputable def tailProd (θ : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∏ i ∈ Finset.range m, Real.sin (θ i) ^ 2







/-- The `k`-th real coordinate of the Euler wave-function for `n` states.
For `k + 1 < n` it carries a trailing cosine; the last coordinate (`k + 1 = n`)
is cosine-free; out of range it is `0`. -/
noncomputable def eulerWave (θ : ℕ → ℝ) (n k : ℕ) : ℝ :=
  if k + 1 < n then (∏ i ∈ Finset.range k, Real.sin (θ i)) * Real.cos (θ k)
  else if k + 1 = n then ∏ i ∈ Finset.range k, Real.sin (θ i)
  else 0

/-- The Born probability `P(k)` of outcome `k` for `n` states. -/
noncomputable def bornProb (θ : ℕ → ℝ) (n k : ℕ) : ℝ :=
  if k + 1 < n then tailProd θ k * Real.cos (θ k) ^ 2
  else if k + 1 = n then tailProd θ k
  else 0







/-
**Any angles give a probability distribution**: the Born probabilities of the
Euler wave-function sum to `1`.
-/




/-- The tail sum `∑_{j=k}^{n-1} p j` — the book's `P(k or above)`. -/
noncomputable def tailSum (p : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico k n, p j









/-
The key construction: given a probability distribution `p`, there exist Euler
angles `θ` whose remainder weights `tailProd θ m` equal the tail sums
`tailSum p n m` for every `m ≤ n`.
-/


/-
**Headline.** For any probability distribution `p` on `{0,…,n-1}` there exist
Euler angles `θ` whose Born probabilities equal `p`: every probability
distribution is reproduced by the Born rule.
-/


end BookProof.ChapterEulerNState


