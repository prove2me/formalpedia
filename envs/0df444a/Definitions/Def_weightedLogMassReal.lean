-- Prove2me | Definitions.Def_weightedLogMassReal
-- name    : weightedLogMassReal
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T02:52:10.567165+00:00
-- url     : https://prove2.me/theorems/7ffc2296-5761-458b-8f38-0b1d583bc9b6
-- title:
--   Real-cutoff logarithmically normalized weighted exceptional sum
-- statement:
--   Sum the weights of admissible exceptional natural-number inputs through the floor of a real cutoff x, then divide by log x. For nonnegative x this includes exactly the natural indices at most x; negative cutoffs are clipped by the natural floor, and density applications use x at least two. The harmonic positive-odd specialization gives the normalized sum in Tao's Theorem 3.1. At natural cutoffs it agrees with weightedLogMass. This is only a definition, not a tail-bound assertion.
-- source:
--   Generalized weighted notation for Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Theorem 3.1, first displayed normalized exceptional sum with real cutoff x. https://arxiv.org/html/1909.03562v7

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped BigOperators
open Classical
noncomputable def weightedLogMassReal (D E : ℕ → Prop) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (⌊x⌋₊ + 1), if D k ∧ E k then w k else 0) / Real.log x


