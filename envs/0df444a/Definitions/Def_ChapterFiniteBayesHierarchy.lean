-- Prove2me | Definitions.Def_ChapterFiniteBayesHierarchy
-- name    : ChapterFiniteBayesHierarchy
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:11:45.39518+00:00
-- url     : https://prove2.me/theorems/2ea842ab-fd4c-46cf-97ef-69ef8681301a
-- title:
--   Chapter FiniteBayesHierarchy
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFiniteBayesHierarchy.lean`): generated def bundle for ChapterFiniteBayesHierarchy. See BookProof/ChapterFiniteBayesHierarchy.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFiniteBayesHierarchy.lean

import Definitions.Def_ChapterHierarchicalBayesComposition
import Mathlib


/-!
# Arbitrary finite Bayesian hierarchies

This module makes the “as many levels as we wish” claim in §11 of
*Aligned deep learning as a random sampling method* (`book.tex` around line
10484) explicit for a homogeneous finite latent-state space.  A list of
conditional kernels is collapsed to one kernel.  The collapse remains a
normalized nonnegative kernel, concatenation becomes kernel composition, and
recursively marginalizing through every level agrees with one marginalization
through the collapsed kernel.
-/

open scoped BigOperators

namespace BookProof.ChapterFiniteBayesHierarchy

open BookProof.ChapterHierarchicalBayesComposition

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Collapse a finite list of transition kernels in temporal order. -/
def collapseKernels : List (S → S → ℝ) → (S → S → ℝ)
  | [] => idKernel
  | k :: ks => compKernel k (collapseKernels ks)











/-- Recursively marginalize a terminal likelihood through all hierarchy levels. -/
def nestedMarginal : List (S → S → ℝ) → (S → ℝ) → (S → ℝ)
  | [], likelihood => likelihood
  | k :: ks, likelihood => terminalMarginal k (nestedMarginal ks likelihood)



end BookProof.ChapterFiniteBayesHierarchy


