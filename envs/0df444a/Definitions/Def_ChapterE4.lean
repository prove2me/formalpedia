-- Prove2me | Definitions.Def_ChapterE4
-- name    : ChapterE4
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:48:24.460288+00:00
-- url     : https://prove2.me/theorems/4adfb3b5-a4e2-4d1c-836b-15960671c775
-- title:
--   Chapter E4
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterE4.lean`): generated def bundle for ChapterE4. See BookProof/ChapterE4.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterE4.lean

import Mathlib


/-!
# Chapter E (continued) — Euler's formula for a *generic* phase-space

This file formalizes the **generic-phase-space** content of the `book.tex`
section *"Euler's formula for a generic phase-space"* (Chapter *"Wave-function
collapse versus Euler's formula"*, `book.tex` line ~3565), complementing:

* `BookProof/ChapterE2.lean` — the stick-breaking *Born probabilities*
  `P(n) = (∏ s²)·c²` (the probability picture), and
* `BookProof/ChapterE3.lean` — the rank-1 density-matrix Euler formula for the
  fixed 2-vector (4-state) case (the density-matrix picture).

The book parametrizes a normalized vector of a separable Hilbert space with a
*countable* orthonormal basis `{lₙ}` by the recursion

```
vₙ = cos(θₙ) · lₙ + sin(θₙ) · vₙ₊₁ ,
```

where `vₙ₊₁` is normalized and orthogonal to `{l₁,…,lₙ}`.  The rank-1 projector
`vₙ vₙ†` then decomposes **recursively** as

```
vₙ vₙ† = cₙ² lₙ lₙ† + sₙ² vₙ₊₁ vₙ₊₁† + cₙ sₙ (lₙ vₙ₊₁† + vₙ₊₁ lₙ†) ,   cₙ = cos θₙ, sₙ = sin θₙ,
```

so *collapse of the wave-function for a generic phase-space is a recursion of
collapses of 2-dimensional real wave-functions*.  Taking the "real part"
(diagonal, in the basis where each `lₙ lₙ†` is diagonal) kills the off-diagonal
cross term, leaving the classical stick-breaking recursion

```
diag(vₙ vₙ†) = cₙ² lₙ lₙ† + sₙ² vₙ₊₁ vₙ₊₁† ,
```

and the conditional probabilities satisfy
`P(n | n or above) + P(n+1 or above | n or above) = cₙ² + sₙ² = 1`, whence total
probability is conserved.

## Model

We take the countable index space to be `ℕ`, the orthonormal basis to be the
standard basis `eₖ = Pi.single k 1 : ℕ → ℝ`, and realize the (finite-support)
recursion terminating after `depth` stick-breaks with base `v = e_{s+depth}`
(`cos = 1`).  Outer products `v v†` are written entrywise as the pointwise
product `v i * v j`.

## Deliverables

* `wave_eq_zero_of_lt` — `vₛ` is supported on indices `≥ s` (orthogonality of the
  tail to the already-measured basis vectors);
* `wave_self_succ` — the leading component is `cos θₛ`;
* `density_recursion` — **headline**: the entrywise density-matrix recursion
  `vₛ vₛ† = cₛ² eₛ eₛ† + sₛ² vₛ₊₁ vₛ₊₁† + cₛ sₛ (eₛ vₛ₊₁† + vₛ₊₁ eₛ†)` (pure
  algebra, no orthonormality);
* `cross_diag_zero` — the Euler cross term `eₛ vₛ₊₁†` has vanishing diagonal;
* `diag_collapse` — "taking the real part": the diagonal obeys the classical
  stick-breaking recursion `(vₛ)ᵢ² = cₛ² (eₛ)ᵢ² + sₛ² (vₛ₊₁)ᵢ²`;
* `cond_prob_sum` — `cₛ² + sₛ² = 1`, the book's
  `P(s | s or above) + P(s+1 or above | s or above) = 1`;
* `wave_prob_sum` — **total probability is conserved**:
  `∑ i ∈ Icc s (s+d), (vₛ)ᵢ² = 1` (the trace of the density matrix is `1`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped BigOperators

namespace BookProof.ChapterE4

/-- Standard basis column vector `eₖ` in the (countable) index space `ℕ`. -/
def basisVec (k : ℕ) : ℕ → ℝ := Pi.single k 1

/-- Recursive real wave-function of the book's *generic phase-space*:
`vₛ = cos θₛ · eₛ + sin θₛ · vₛ₊₁`, terminating after `depth` stick-breaks with
base `v = e_{s+depth}` (`cos = 1`).  `wave θ s d` is the wave-function whose
leading component is at index `s` and which has `d` remaining stick-breaks. -/
noncomputable def wave (θ : ℕ → ℝ) : ℕ → ℕ → (ℕ → ℝ)
  | s, 0 => basisVec s
  | s, (d + 1) =>
      fun i => Real.cos (θ s) * basisVec s i + Real.sin (θ s) * wave θ (s + 1) d i





/-
`(eₖ)ᵢ² = if i = k then 1 else 0`.
-/


/-
The tail wave-function `vₛ` is supported only on indices `≥ s`: it is
orthogonal to each already-measured basis vector `l₁,…,lₛ`.
-/


/-
The leading component of `vₛ` (after at least one stick-break) is `cos θₛ`.
-/


/-
**Headline — density-matrix recursion (Euler's formula for a generic
phase-space).**  Entrywise,
`vₛ vₛ† = cₛ² eₛ eₛ† + sₛ² vₛ₊₁ vₛ₊₁† + cₛ sₛ (eₛ vₛ₊₁† + vₛ₊₁ eₛ†)`.
This is a purely algebraic identity, requiring no orthonormality.
-/


/-
The Euler cross term `eₛ vₛ₊₁†` has a vanishing diagonal: `(eₛ)ᵢ · (vₛ₊₁)ᵢ = 0`
for every `i` (if `i = s` then `(vₛ₊₁)ₛ = 0` by orthogonality, else `(eₛ)ᵢ = 0`).
-/


/-
**Collapse = taking the real part.**  The diagonal of `vₛ vₛ†` obeys the
classical stick-breaking recursion `(vₛ)ᵢ² = cₛ² (eₛ)ᵢ² + sₛ² (vₛ₊₁)ᵢ²`: the
off-diagonal cross term drops out on the diagonal.
-/


/-
The book's conditional-probability identity
`P(s | s or above) + P(s+1 or above | s or above) = 1`, i.e. `cₛ² + sₛ² = 1`.
-/


/-
**Total probability is conserved** (the trace of the density matrix is `1`):
`∑ i ∈ Icc s (s+d), (vₛ)ᵢ² = 1`.  Equivalently `tr(diag(vₛ vₛ†)) = 1`.
-/


end BookProof.ChapterE4


