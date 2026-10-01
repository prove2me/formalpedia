-- Prove2me | Definitions.Def_ChapterUniformPrior
-- name    : ChapterUniformPrior
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:46:36.825401+00:00
-- url     : https://prove2.me/theorems/9239b3af-12bc-4046-baa4-afcec0f3e531
-- title:
--   Chapter UniformPrior
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterUniformPrior.lean`): generated def bundle for ChapterUniformPrior. See BookProof/ChapterUniformPrior.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUniformPrior.lean

import Definitions.Def_ChapterBayesInference
import Mathlib


/-!
# Uniform priors, relabeling symmetry, and maximum likelihood

This file formalizes two adjacent finite claims from the Bayesian chapters of
`book.tex` (around lines 1710--1720 and 9125--9450):

* a prior that treats every relabeling of a finite hypothesis space identically
  must be uniform; and
* with a positive uniform prior, maximizing the posterior is exactly maximizing
  the likelihood.

Thus the finite uniform prior is characterized by complete label symmetry, and
its MAP rule is the maximum-likelihood rule.  The broader philosophical claims
about non-informative priors are left as prose.
-/

open scoped BigOperators

namespace BookProof.ChapterUniformPrior

variable {Hyp Data : Type*}

/-- A weight function is invariant under every relabeling of hypotheses. -/
def IsRelabelingInvariant (p : Hyp → ℝ) : Prop :=
  ∀ σ : Equiv.Perm Hyp, p ∘ σ = p

/-
Complete relabeling invariance forces all hypothesis weights to coincide.
-/


/-
Relabeling invariance is equivalent to being a constant weight function.
-/


/-
On a nonempty finite space, the normalized relabeling-invariant prior is
uniquely the uniform distribution `1 / |Hyp|`.
-/


/-
A positive uniform prior preserves every pairwise likelihood comparison in
its posterior, provided the observed datum has positive evidence.
-/


/-
Consequently, under a positive uniform prior a hypothesis is MAP exactly
when it is a maximum-likelihood hypothesis.
-/


end BookProof.ChapterUniformPrior


