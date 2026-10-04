-- Prove2me | Definitions.Def_ChapterFreeFieldBornFiberSpectrum
-- name    : ChapterFreeFieldBornFiberSpectrum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:35:49.875984+00:00
-- url     : https://prove2.me/theorems/19d6094b-de2d-4e69-a2e9-645938377585
-- title:
--   Chapter FreeFieldBornFiberSpectrum
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFreeFieldBornFiberSpectrum.lean`): generated def bundle for ChapterFreeFieldBornFiberSpectrum. See BookProof/ChapterFreeFieldBornFiberSpectrum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeFieldBornFiberSpectrum.lean

import Definitions.Def_ChapterA4
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the full spectrum of Born-fiber cardinalities

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the free-field construction of §5 (`book.tex` ~line 1706) and the
Introduction's remark (`book.tex` ~line 805) that the wave function is *one
possible* parametrization of a probability distribution.

Waves 151–155 computed the exact Born-fiber count
`Nat.card (bornMapSphere ⁻¹' {p}) = 2 ^ (#positive coordinates of p)`, gave the
sharp two-sided bound `2 ≤ #fiber ≤ 2ⁿ`, and characterized the two extremes.

This wave records the **structural shape** of the fiber cardinality and pins
down the *entire spectrum* of values it takes:

* every fiber size is an **even power of two** dividing `2ⁿ`;
* the fiber size is **monotone** in the positive support;
* and — building an explicit `k`-point uniform distribution — **every** value
  `2ᵏ` with `1 ≤ k ≤ n` is attained, and no others.  Hence the set of achievable
  fiber cardinalities is exactly `{2ᵏ : 1 ≤ k ≤ n}`.

## Main results

* `bornFiber_card_even` — `2 ∣ #fiber`.
* `bornFiber_card_isPowerOfTwo` — `∃ k, 1 ≤ k ∧ k ≤ n ∧ #fiber = 2 ^ k`.
* `bornFiber_card_dvd_two_pow_n` — `#fiber ∣ 2 ^ n`.
* `bornFiber_card_mono` — `posSupport p ⊆ posSupport q → #fiber p ≤ #fiber q`.
* `unifDist` — the uniform distribution on the first `k` coordinates, with
  `posSupport` of cardinality `k`.
* `exists_bornFiber_card_eq_two_pow` — for `1 ≤ k ≤ n` some distribution has
  fiber cardinality `2 ^ k`.
* **headline** `bornFiber_card_achievable_iff` — a number `c` is the cardinality
  of some Born fiber iff `c = 2 ^ k` for some `1 ≤ k ≤ n`.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory

namespace BookProof.ChapterFreeFieldBornFiberSpectrum

variable {n : ℕ}

/-
Every Born fiber has an even number of points: the global `±1` sign is
always a free involution, so the exponent `#positive coords` is at least `1`.
-/


/-
The Born-fiber cardinality is a power of two with exponent between `1` and
`n`: exactly `2 ^ (#positive coords)` with `1 ≤ #positive coords ≤ n`.
-/




/-
The Born-fiber cardinality is monotone in the positive support: a
distribution with a larger positive support has at least as many wave
functions.
-/


/-- The uniform distribution supported on the first `k` coordinates. -/
noncomputable def unifDist (n k : ℕ) : Fin n → ℝ :=
  fun j => if (j : ℕ) < k then (1 : ℝ) / k else 0

/-
For `1 ≤ k ≤ n`, `unifDist n k` is a probability distribution.
-/


/-
For `1 ≤ k ≤ n`, `unifDist n k` has exactly `k` strictly positive
coordinates.
-/


/-
For every `1 ≤ k ≤ n` there is a probability distribution whose Born fiber
has exactly `2 ^ k` points — the uniform distribution on the first `k`
coordinates.
-/


/-
**Headline.** The set of achievable Born-fiber cardinalities is exactly
`{2 ^ k : 1 ≤ k ≤ n}`: a number `c` is the cardinality of some Born fiber iff
`c = 2 ^ k` for some `k` with `1 ≤ k ≤ n`.
-/


end BookProof.ChapterFreeFieldBornFiberSpectrum


