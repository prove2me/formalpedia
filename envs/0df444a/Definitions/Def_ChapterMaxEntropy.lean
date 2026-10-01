-- Prove2me | Definitions.Def_ChapterMaxEntropy
-- name    : ChapterMaxEntropy
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:23:20.993997+00:00
-- url     : https://prove2.me/theorems/a84e5ac3-edc9-480b-885d-c921a38b55d6
-- title:
--   Chapter MaxEntropy
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMaxEntropy.lean`): generated def bundle for ChapterMaxEntropy. See BookProof/ChapterMaxEntropy.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMaxEntropy.lean

import Mathlib


/-!
# Chapter "Aligned deep learning as a random sampling method", §2
"Systematic uncertainties and Bayesian priors" / Chapter "Consciousness as a
representation of a Bayesian prior" — **the maximum-entropy characterization of
the uniform (non-informative) prior**

Source: `book.tex`.  The book repeatedly appeals to the *maximum-entropy* /
*non-informative prior* principle, e.g.

> *"tools and techniques of automated reasoning include … Bayesian inference,
> reasoning with **maximal entropy** and many less formal ad hoc techniques."*
> (`book.tex` line ~9772)

and it stresses that *"there are no non-informative priors and there are no
almost non-informative priors"* (`book.tex` lines ~9349, ~9451): the closest one
gets to a "non-informative" prior on a finite sample space is the **uniform**
distribution, and the precise sense in which it is the least informative is that
it **maximizes the Shannon entropy**.

This module formalizes that self-contained, classical mathematical fact,
entirely independent of the surrounding discussion.  For a finite probability
distribution `p` on a (nonempty) finite sample space `α` with `n = |α|` outcomes,
the Shannon entropy `H(p) = ∑ᵢ −pᵢ log pᵢ` satisfies

* `entropy_nonneg`   — `0 ≤ H(p)`;
* `entropy_le_log_card` — `H(p) ≤ log n` (the maximum-entropy bound, via the
  Gibbs inequality `log x ≤ x − 1`);
* `entropy_uniform`  — the uniform distribution attains it: `H(uniform) = log n`;
* HEADLINE `entropy_le_entropy_uniform` — hence the uniform distribution is the
  **maximum-entropy** distribution: `H(p) ≤ H(uniform)` for every distribution
  `p`;
* `entropy_eq_log_card_iff` — the uniform prior is the **unique** maximizer:
  `H(p) = log n` iff `p` is the uniform distribution (via the strict Gibbs
  inequality `log x < x − 1` for `x ≠ 1`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Real BigOperators Finset

namespace BookProof.ChapterMaxEntropy

variable {α : Type*} [Fintype α]

/-- A finite probability distribution: nonnegative weights summing to one. -/
structure IsProb (p : α → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_one : ∑ i, p i = 1

/-- The **Shannon entropy** of a finite distribution `p`, using Mathlib's
`Real.negMulLog x = -x * log x` (so `H(p) = ∑ᵢ −pᵢ log pᵢ`). -/
noncomputable def entropy (p : α → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- The **uniform** distribution on `α`: every outcome carries weight `1/|α|`. -/
noncomputable def uniform (α : Type*) [Fintype α] : α → ℝ :=
  fun _ => (Fintype.card α : ℝ)⁻¹



















end BookProof.ChapterMaxEntropy


