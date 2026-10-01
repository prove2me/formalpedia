-- Prove2me | Definitions.Def_ChapterEntropy
-- name    : ChapterEntropy
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:49:17.205293+00:00
-- url     : https://prove2.me/theorems/818d3277-5e3c-4f9c-8fc1-3244ed34750b
-- title:
--   Chapter Entropy
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterEntropy.lean`): generated def bundle for ChapterEntropy. See BookProof/ChapterEntropy.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEntropy.lean

import Mathlib


/-!
# Chapter — Entropy and an irreversible deterministic time-evolution coexist

Source: `book.tex`, chapter *"Entropy and an irreversible deterministic
time-evolution coexist"* (line ~9474), §"Irreversible deterministic
time-evolution".

The book rescales the joint sample space to the square `[0,1]×[0,1]`, partitions
it into `n²` equal cells, and observes that the probability that a uniformly
random *discrete* self-map of the `n` index cells is **invertible** (a bijection)
equals `n!/nⁿ`; that by Stirling this is asymptotic to `√(2πn) e^{-n}`; and that
it therefore **tends to `0`** as `n → ∞`.  Consequently a randomly sampled
time-evolution is almost surely a non-invertible map (injective but not
surjective) — an irreversible, dissipative deterministic dynamical system — which
is the book's mechanism for the arrow of time coexisting with time-symmetric
laws.

This file formalizes those self-contained mathematical claims:

* `card_selfMaps` / `card_bijections` — there are `nⁿ` self-maps and `n!`
  bijections of an `n`-element index set;
* `invertibleProb` — the invertibility probability, defined as the ratio of the
  two counts, and `invertibleProb_eq` — it equals `(n! : ℝ)/nⁿ`;
* `invertibleProb_nonneg` / `invertibleProb_le_one` — it is a genuine
  probability, lying in `[0,1]` (using `Nat.factorial_le_pow`);
* **headline** `invertibleProb_tendsto_zero` — it tends to `0`;
* `invertibleProb_isEquivalent_stirling` — the Stirling asymptotic
  `n!/nⁿ ~ √(2πn) e^{-n}` (the book's stated equivalent);
* `exists_injective_not_surjective` — on the countable index set `ℕ` there is a
  deterministic map that is injective (non-singular) but not surjective (not
  invertible): a concrete irreversible-dynamics / arrow-of-time witness.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterEntropy

open Filter Asymptotics
open scoped Topology





/-- The probability that a uniformly random discrete self-map of the `n` index
cells is invertible: the number of bijections divided by the number of
self-maps. -/
noncomputable def invertibleProb (n : ℕ) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ) / (Fintype.card (Fin n → Fin n) : ℝ)









/-
The book's Stirling asymptotic for the invertibility probability:
`n!/nⁿ ~ √(2πn) e^{-n}` as `n → ∞`.  Obtained from Mathlib's Stirling formula
`Stirling.factorial_isEquivalent_stirling` by dividing through by `nⁿ` and
simplifying `(n/e)ⁿ / nⁿ = e^{-n}`.
-/




end BookProof.ChapterEntropy


