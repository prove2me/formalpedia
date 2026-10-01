-- Prove2me | Definitions.Def_ChapterPriorDependence
-- name    : ChapterPriorDependence
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:29:04.436565+00:00
-- url     : https://prove2.me/theorems/f6b21614-09a6-45b7-a77a-d0ad11dddec4
-- title:
--   Chapter PriorDependence
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPriorDependence.lean`): generated def bundle for ChapterPriorDependence. See BookProof/ChapterPriorDependence.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPriorDependence.lean

import Definitions.Def_ChapterBayesInference
import Mathlib


/-!
# Book chapter "Consciousness as a representation of a Bayesian prior"

This file formalizes the elementary Bayesian core of §"A deterministic prior is
still subjective" (`book.tex` lines 9208–9267).  A deterministic prior is a
Dirac mass.  Conditioning it on data of positive likelihood leaves it a Dirac
mass; choosing a different deterministic prior can therefore give a different
posterior from the same likelihood and observation.

The philosophical discussion surrounding these identities remains prose.
-/

open scoped BigOperators

namespace BookProof.ChapterPriorDependence

variable {Hyp Data : Type*} [DecidableEq Hyp]

/-- Deterministic (Dirac) prior concentrated at `a`. -/
def diracPrior (a : Hyp) (x : Hyp) : ℝ := if x = a then 1 else 0



variable [Fintype Hyp]



/-
Evidence under a deterministic prior is just the likelihood at its support.
-/


/-
Positive-likelihood Bayesian updating preserves a deterministic prior.
-/


/-
Two distinct deterministic prior assumptions yield distinct posteriors for
the same data whenever the first supported hypothesis has positive likelihood.
-/


end BookProof.ChapterPriorDependence


