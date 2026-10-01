-- Prove2me | Definitions.Def_ChapterMarkovEntropy
-- name    : ChapterMarkovEntropy
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:23:21.569987+00:00
-- url     : https://prove2.me/theorems/d12da2d0-a180-4f3c-a8fc-cfd078086412
-- title:
--   Chapter MarkovEntropy
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMarkovEntropy.lean`): generated def bundle for ChapterMarkovEntropy. See BookProof/ChapterMarkovEntropy.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMarkovEntropy.lean

import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §2
"Probability updates, machine learning and Quantum Mechanics":
**Markov processes are entropy-monotone, hence Bayesian inference is irreversible**

Formalization of the self-contained mathematical claim the book makes in §2 of its
central foundational chapter (`book.tex` line ~1338), where it contrasts its
*reversible* "Unitary inference" with ordinary Bayesian inference:

> "Markov processes cannot produce an arbitrary function of time, because there
> is an ordering (related with the concept of entropy) with respect to which all
> continuous-time Markov processes are monotonic.  Thus, Bayesian inference is
> irreversible."

The self-contained finite-dimensional content is the classical **entropy
increase under a doubly-stochastic (bistochastic) Markov map** (the discrete
`H`-theorem): applying such a Markov transition matrix `M` to a probability
vector `p` can only *increase* the Shannon entropy, `H(p) ≤ H(M p)`, with
equality (reversibility) for a **permutation** matrix — a deterministic,
invertible transition.  So the entropy ordering is monotone along any Markov
process, and can be preserved only by the reversible (permutation) maps; a
genuinely mixing Markov step cannot be undone.  This is exactly the
irreversibility the book invokes to motivate unitary inference.

The proof is Jensen's inequality for the concave function `negMulLog x = -x·log x`
(`Real.concaveOn_negMulLog`), applied row by row, together with the two
stochasticity constraints.

Consistently with the finite-dimensional models used throughout `BookProof`, the
statement is over finite index sets `Fin n`.  This file is `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators
open Finset

namespace BookProof.ChapterMarkovEntropy

variable {n : ℕ}

/-- Shannon entropy of a finite probability vector `p : Fin n → ℝ`,
`H(p) = ∑_a -p a · log (p a)`. -/
noncomputable def entropy (p : Fin n → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

/-- The action of a Markov transition matrix `M` (with `M j i` the probability of
moving from state `i` to state `j`) on a probability vector `p`:
`(M p) j = ∑_i M j i · p i`. -/
def applyMarkov (M : Fin n → Fin n → ℝ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i, M j i * p i

/-- A **doubly stochastic** (bistochastic) transition matrix: nonnegative entries
whose rows and columns both sum to one. -/
structure IsDoublyStochastic (M : Fin n → Fin n → ℝ) : Prop where
  nonneg : ∀ j i, 0 ≤ M j i
  colSum : ∀ i, ∑ j, M j i = 1
  rowSum : ∀ j, ∑ i, M j i = 1



/-- The permutation matrix of `σ`: `M j i = 1` iff `j = σ i`, else `0`.  This
models a *deterministic, invertible* (reversible) transition. -/
def permMatrix (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → ℝ :=
  fun j i => if j = σ i then 1 else 0







end BookProof.ChapterMarkovEntropy


