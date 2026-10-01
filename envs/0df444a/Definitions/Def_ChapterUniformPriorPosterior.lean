-- Prove2me | Definitions.Def_ChapterUniformPriorPosterior
-- name    : ChapterUniformPriorPosterior
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:46:56.525809+00:00
-- url     : https://prove2.me/theorems/144f4dad-4ede-47d1-8e1f-eb8dc9565d8a
-- title:
--   Chapter UniformPriorPosterior
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterUniformPriorPosterior.lean`): generated def bundle for ChapterUniformPriorPosterior. See BookProof/ChapterUniformPriorPosterior.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUniformPriorPosterior.lean

import Definitions.Def_ChapterBayesInference
import Mathlib


/-!
# Every finite prior is a posterior from uniform prior and suitable data

This file formalizes the next self-contained Bayesian claim in `book.tex` around
lines 1749--1760: results obtained from a non-uniform prior can be represented
using a uniform prior with suitable data.

For a finite target distribution `q`, use binary data and the likelihood
`L x true = q x`, `L x false = 1 - q x`.  Every row of `L` is a probability
distribution.  Conditioning any positive constant (uniform) prior on `true`
then returns exactly `q`.
-/

open scoped BigOperators

namespace BookProof.ChapterUniformPriorPosterior

variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

/-- Binary likelihood whose `true` probability is the prescribed weight. -/
def binaryLikelihood (q : Hyp → ℝ) (x : Hyp) (observed : Bool) : ℝ :=
  if observed then q x else 1 - q x













end BookProof.ChapterUniformPriorPosterior


