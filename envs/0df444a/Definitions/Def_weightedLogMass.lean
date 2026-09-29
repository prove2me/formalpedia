-- Prove2me | Definitions.Def_weightedLogMass
-- name    : weightedLogMass
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T02:37:33.510258+00:00
-- url     : https://prove2.me/theorems/55156b3f-14c9-48a3-ae76-9fb0a29a9971
-- title:
--   Logarithmically normalized weighted exceptional sum
-- statement:
--   For an admissible domain D, an exceptional set E, and real weights w, sum w(n) over the admissible exceptional integers from zero through the integer cutoff, then divide by the logarithm of the cutoff. In logarithmic-density applications D excludes zero, w(n) = 1/n, and cutoffs are at least two. This is a generalized weighted interface, not itself a density limit or a Collatz assertion.
-- source:
--   Generalized weighted notation for the normalized exceptional sums in Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Section 3, Theorem 3.1 and deduction of Theorem 1.6. https://arxiv.org/html/1909.03562v7 . Here cutoffs are natural numbers and weights/domain are abstract; the harmonic odd-input specialization is the source application.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
open Classical

noncomputable def weightedLogMass (D E : ℕ → Prop) (w : ℕ → ℝ) (cutoff : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (cutoff + 1), if D k ∧ E k then w k else 0) /
    Real.log (cutoff : ℝ)


