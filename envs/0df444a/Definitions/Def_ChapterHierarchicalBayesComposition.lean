-- Prove2me | Definitions.Def_ChapterHierarchicalBayesComposition
-- name    : ChapterHierarchicalBayesComposition
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:02:27.697961+00:00
-- url     : https://prove2.me/theorems/5769aff8-a5b2-49ac-8d75-6f3873b19870
-- title:
--   Chapter HierarchicalBayesComposition
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHierarchicalBayesComposition.lean`): generated def bundle for ChapterHierarchicalBayesComposition. See BookProof/ChapterHierarchicalBayesComposition.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHierarchicalBayesComposition.lean

import Definitions.Def_ChapterHierarchicalBayes
import Mathlib


/-!
# Composition of finite Bayesian hierarchies

This module continues the formalization of §11 of "Aligned deep learning as a
random sampling method" (`book.tex` around line 10484).  The book says that a
hierarchical inference problem may have as many levels as desired.  The earlier
`ChapterHierarchicalBayes` treats two levels.  Here finite conditional kernels
are equipped with an associative composition operation.  Closure under
normalization and nonnegativity, together with associativity and the
marginalization law, makes arbitrary finite hierarchies compositional: adjacent
levels may be collapsed in any order without changing the resulting likelihood.
-/

open scoped BigOperators

namespace BookProof.ChapterHierarchicalBayesComposition

variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Composition of two finite conditional kernels, obtained by summing out the
intermediate state. -/
def compKernel (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (a : A) (c : C) : ℝ :=
  ∑ b, k₁ a b * k₂ b c

/-- A finite conditional kernel is normalized at every input. -/
def IsNormalizedKernel (k : A → B → ℝ) : Prop :=
  ∀ a, ∑ b, k a b = 1

/-- A finite conditional kernel is pointwise nonnegative. -/
def IsNonnegativeKernel (k : A → B → ℝ) : Prop :=
  ∀ a b, 0 ≤ k a b







/-- The identity conditional kernel. -/
def idKernel (a a' : A) : ℝ := if a = a' then 1 else 0









/-- Marginalize a terminal likelihood through one finite conditional kernel. -/
def terminalMarginal (k : A → B → ℝ) (likelihood : B → ℝ) (a : A) : ℝ :=
  ∑ b, k a b * likelihood b





end BookProof.ChapterHierarchicalBayesComposition


