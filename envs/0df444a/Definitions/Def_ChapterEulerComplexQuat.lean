-- Prove2me | Definitions.Def_ChapterEulerComplexQuat
-- name    : ChapterEulerComplexQuat
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:50:26.666308+00:00
-- url     : https://prove2.me/theorems/5671b703-29b5-4d98-9d02-49fca5dab02c
-- title:
--   Chapter EulerComplexQuat
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterEulerComplexQuat.lean`): generated def bundle for ChapterEulerComplexQuat. See BookProof/ChapterEulerComplexQuat.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEulerComplexQuat.lean

import Mathlib


/-!
# Chapter "Wave-function collapse versus Euler's formula", §"Complex and
Quaternionic Hilbert spaces" — the complex/quaternionic Born distribution is
the realification of a real one

This file formalizes the self-contained mathematical content of the subsection
*"Complex and Quaternionic Hilbert spaces"* of the chapter *"Wave-function
collapse versus Euler's formula"* (`book.tex`, §"Euler's formula for a generic
phase-space", line ~3639):

> *"While the parametrization with a real wave-function is always possible, it
> may not be the best one. … Let us consider the quaternionic case … We have a
> discrete state space defined by two real numbers `n,m`, with `1 ≤ m ≤ 4` and
> we only consider the probabilities for `n` independently of `m`,
> `P(n) = ∑_{m=1}^4 P(n,m)`. … The complex case is just the above case with
> complex numbers replacing quaternions and a state space which is the union of
> 2 identical spaces."*

The book's point is that a complex (resp. quaternionic) wave-function is the
*realification* of a real wave-function on a state space with twice (resp. four
times) as many outcomes, and the complex/quaternionic **Born probability**
`P(n) = |vₙ|²` is exactly the sum of the `2` (resp. `4`) real Born
probabilities of the underlying real coordinates:
`|z|² = (Re z)² + (Im z)²` and `|q|² = q_re² + q_i² + q_j² + q_k²`.  Because the
real Euler-angle parametrization (`ChapterEulerNState`) reproduces *any*
probability distribution, so do the complex and quaternionic ones.

This complements `ChapterEulerNState` (real case), `ChapterEulerStochastic`
(2-state), and `ChapterE3` (density-matrix Euler formula).

We model a `n`-outcome wave-function as a vector `Fin n → 𝕜` (`𝕜 = ℝ, ℂ, ℍ[ℝ]`)
and its Born distribution as `k ↦ ‖vₖ‖²`.  Everything is `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).

Deliverables:
* `complex_born_split` / `quat_born_split` — `P(n) = ∑_m P(n,m)` with `m` ranging
  over the `2` (resp. `4`) real coordinates;
* `complex_realification_norm` / `quat_realification_norm` — the realification
  preserves total probability (unit norm);
* `complex_reproduces` / `quat_reproduces` — every probability distribution is
  reproduced by the Born rule of a complex (resp. quaternionic) unit
  wave-function.
-/

open scoped Quaternion BigOperators

namespace BookProof.ChapterEulerComplexQuat

variable {n : ℕ}

/-! ## Complex case: state space is the union of `2` identical real spaces -/

/-- The complex Born probability of outcome `k`, `P(k) = |v k|²`. -/
noncomputable def cbornProb (v : Fin n → ℂ) (k : Fin n) : ℝ := Complex.normSq (v k)









/-! ## Quaternionic case: state space `(n, m)` with `1 ≤ m ≤ 4` -/

/-- The quaternionic Born probability of outcome `k`, `P(k) = |v k|²`. -/
noncomputable def qbornProb (v : Fin n → ℍ[ℝ]) (k : Fin n) : ℝ := Quaternion.normSq (v k)









end BookProof.ChapterEulerComplexQuat


