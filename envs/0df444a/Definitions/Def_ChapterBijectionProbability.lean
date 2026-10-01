-- Prove2me | Definitions.Def_ChapterBijectionProbability
-- name    : ChapterBijectionProbability
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:25:19.143989+00:00
-- url     : https://prove2.me/theorems/42f361c2-7c5b-473a-9dae-7f17f68a9714
-- title:
--   Chapter BijectionProbability
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterBijectionProbability.lean`): generated def bundle for ChapterBijectionProbability. See BookProof/ChapterBijectionProbability.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBijectionProbability.lean

import Mathlib


/-!
# Chapter "Entropy and an irreversible deterministic time-evolution coexist",
§"Irreversible deterministic time-evolution" — the probability that a random
discrete map on an `n`-cell partition is invertible

Source: `book.tex`, chapter *"Entropy and an irreversible deterministic
time-evolution coexist"*, §*"Irreversible deterministic time-evolution"*
(`book.tex` line ~9540):

> *"We rescale the square to `[0,1]×[0,1]`. If we partition the square in `n²`
> smaller equal sized squares, then the probability of an invertible discrete
> function (whose domain and image is the index of an interval in the partition)
> is `n!/nⁿ ∼ √(2πn) e^{-n}` (as `n` goes to infinity, the ratio between the left
> and right sides approaches one in the limit). Thus it converges to `0` when
> `n → +∞`."*

The self-contained mathematical content, independent of the surrounding physics,
is a discrete-probability / asymptotics fact.  A "discrete function" on the
`n`-cell index set is an arbitrary map `Fin n → Fin n`; it is "invertible" iff it
is a bijection.  Choosing such a map uniformly at random, the probability of
landing on a bijection is

  `(number of bijections) / (number of functions) = n! / nⁿ`,

and the book asserts (i) this equals `n!/nⁿ`, (ii) it is asymptotically
`√(2πn) e^{-n}` (Stirling), and (iii) it converges to `0`.

## Deliverables

* `card_fun_fin` — there are `nⁿ` functions `Fin n → Fin n`.
* `card_bijective_fin` — there are `n!` bijective functions `Fin n → Fin n`.
* `bijProb` — the probability `n!/nⁿ`.
* `bijProb_eq_card_ratio` — `bijProb n` is the ratio (bijections)/(functions).
* `factorial_succ_le` — the elementary bound `(n+1)! ≤ (n+1)ⁿ`.
* `bijProb_nonneg`, `bijProb_le_one_div` — `0 ≤ bijProb n ≤ 1/n`.
* `bijProb_tendsto_zero` — **the book's "converges to `0`"**: `bijProb n → 0`.
* `bijProb_isEquivalent_stirling` — **the book's `∼ √(2πn) e^{-n}`**:
  `bijProb` is asymptotically equivalent to `n ↦ √(2πn) · e^{-n}` (from
  Mathlib's Stirling formula).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped Nat
open Filter Asymptotics

namespace BookProof.ChapterBijectionProbability



/-- The invertible ("bijective") discrete functions `Fin n → Fin n` correspond
bijectively to the permutations of `Fin n`. -/
noncomputable def permEquivBijective (n : ℕ) :
    Equiv.Perm (Fin n) ≃ {f : Fin n → Fin n // Function.Bijective f} where
  toFun σ := ⟨σ, σ.bijective⟩
  invFun f := Equiv.ofBijective f.1 f.2
  left_inv σ := by ext x; rfl
  right_inv f := by ext x; rfl



/-- The probability that a uniformly random discrete function `Fin n → Fin n`
is invertible: `n!/nⁿ`. -/
noncomputable def bijProb (n : ℕ) : ℝ := (n ! : ℝ) / (n : ℝ) ^ n













end BookProof.ChapterBijectionProbability


