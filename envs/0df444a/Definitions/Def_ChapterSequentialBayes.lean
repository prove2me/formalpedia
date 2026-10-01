-- Prove2me | Definitions.Def_ChapterSequentialBayes
-- name    : ChapterSequentialBayes
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:37:28.618333+00:00
-- url     : https://prove2.me/theorems/07257fb7-7428-4e32-9fd4-ea8829ab9e7d
-- title:
--   Chapter SequentialBayes
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSequentialBayes.lean`): generated def bundle for ChapterSequentialBayes. See BookProof/ChapterSequentialBayes.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSequentialBayes.lean

import Definitions.Def_ChapterBayesInference
import Mathlib


/-!
# Chapter "Aligned deep learning as a random sampling method", §3
"Bayesian inference in the presence of Big Data" — **sequential Bayesian updating
equals batch updating**

Source: `book.tex`.  The book stresses (chapter *"Aligned deep learning as a
random sampling method"*, §3, `book.tex` line ~9858) that

> *"Bayesian inference is still valid in the presence of Big Data, since it is
> valid for an arbitrarily large number of random variables, as long as it is a
> finite number."*

and (§2, `book.tex` line ~9803) that a brain does *"Bayesian learning in a
standard probability space … where the posterior probability is the output"*.

The precise, self-contained mathematical fact underlying "validity for an
arbitrarily large but finite number of observations" is the **coherence
(associativity) of Bayesian updating**: processing observations *one at a time*
(using each posterior as the prior for the next update) yields *exactly* the same
final posterior as processing them *all at once* in a single batch update, as
long as the observations are conditionally independent given the hypothesis
(so their likelihoods multiply).  Consequently a Bayesian learner can ingest an
arbitrarily long finite stream of data sequentially without any loss compared to
the (usually intractable) batch computation.

This module formalizes that fact.  For a finite hypothesis space `X`, a prior
`prior : X → ℝ` and a likelihood weight `ℓ : X → ℝ` (the value `ℓ x = L(x, y)`
of the likelihood at the observed data `y`), the **Bayes update** is

`bayesUpdate prior ℓ x = prior x · ℓ x / (∑_{x'} prior x' · ℓ x')`.

Deliverables (all `sorry`-free, `axiom`-free):

* `bayesUpdate_nonneg` — the updated distribution is nonnegative;
* `bayesUpdate_sum_one` — with positive evidence it is a probability distribution;
* `bayesUpdate_evidence` — the intermediate second-step evidence factorizes as
  `(∑ prior·ℓ₁·ℓ₂) / (∑ prior·ℓ₁)`;
* HEADLINE `sequential_eq_batch` — updating on `ℓ₁` and then on `ℓ₂` equals the
  single batch update on the product likelihood `ℓ₁ · ℓ₂`;
* `posterior_eq_bayesUpdate` — the book's `ChapterBayesInference.posterior`
  observing data `y` is exactly `bayesUpdate` with the likelihood column
  `x ↦ L x y`, so the coherence result transfers verbatim to that framework;
* `posterior_sequential_eq_batch` — the same coherence statement phrased with
  `posterior` and a conditionally-independent (product) two-observation
  likelihood.
-/

open scoped BigOperators

namespace BookProof.ChapterSequentialBayes

variable {X : Type*} [Fintype X]

/-- The **Bayes update** of a prior `prior : X → ℝ` by a likelihood weight
`ℓ : X → ℝ`: the (normalized) posterior `x ↦ prior x · ℓ x / ∑_{x'} prior x' · ℓ x'`. -/
noncomputable def bayesUpdate (prior ℓ : X → ℝ) : X → ℝ :=
  fun x => prior x * ℓ x / (∑ x', prior x' * ℓ x')

/-- The (batch) evidence `∑_x prior x · ℓ x`. -/
def totEvidence (prior ℓ : X → ℝ) : ℝ := ∑ x, prior x * ℓ x













end BookProof.ChapterSequentialBayes


