-- Prove2me | Definitions.Def_ChapterInverseTransform
-- name    : ChapterInverseTransform
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:12:09.120322+00:00
-- url     : https://prove2.me/theorems/99c01e36-3abc-4840-8133-257ad150dc3a
-- title:
--   Chapter InverseTransform
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterInverseTransform.lean`): generated def bundle for ChapterInverseTransform. See BookProof/ChapterInverseTransform.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterInverseTransform.lean

import Mathlib


/-!
# Chapter — A deterministic theory compatible with relativistic Quantum Mechanics

Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any isolated
quantum system"*, §*"A deterministic theory compatible with relativistic Quantum
Mechanics"* (line ~2952).

The book answers, constructively, the question *"Does a deterministic theory —
consistent with the non-deterministic time evolution of Quantum Mechanics —
exist?"* with **yes**, exhibiting one such theory built on the
**inverse-transform sampling** method:

> *"In an experimental setting, we always have a discrete set of possible outcomes
> and thus Quantum Mechanics always predicts a cumulative distribution function.
> This allows us to apply the inverse-transform sampling method for generating
> pseudo-random numbers consistently with the probability distribution predicted
> by Quantum Mechanics."*

This file formalizes the mathematical backbone of that construction: for a
discrete probability distribution `p : ℕ → ℝ` on the outcomes `0, …, n-1`
(`p i ≥ 0`, `∑_{i<n} p i = 1`), the **cumulative distribution function**
`cdf p k = ∑_{i<k} p i` partitions the seed interval `[0,1)` into the half-open
"seed" intervals `seedSet k = [cdf p k, cdf p (k+1))`, one per outcome, such that:

* `seedSet_measure`  — the Lebesgue measure of `seedSet k` is exactly `p k`, so a
  **uniformly** drawn seed produces outcome `k` with probability `p k`: the
  deterministic decoder reproduces the quantum probability distribution;
* `seedSet_disjoint` — the seed intervals are pairwise disjoint (each seed yields
  at most one outcome);
* `seedSet_cover`    — the seed intervals for `k < n` cover `[0,1)` exactly (each
  seed yields at least one outcome);
* `seedSet_total_measure` — the seed intervals carry total measure `1`.

Together these say that `seed ↦ (the unique k < n with seed ∈ seedSet k)` is a
well-defined *deterministic* map `[0,1) → {0,…,n-1}` whose pushforward of the
uniform seed distribution is precisely the quantum distribution `p` — a
deterministic theory experimentally indistinguishable from Quantum Mechanics, as
the book claims. (The physical/metaphysical discussion around the construction is
prose and out of scope.)
-/

namespace BookProof.InverseTransform

open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

/-- The **cumulative distribution function** of the discrete distribution `p`:
`cdf p k = ∑_{i<k} p i`.  This is the CDF the book says Quantum Mechanics always
predicts in an experimental setting with discretely many outcomes. -/
def cdf (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, p i

/-- The **seed interval** for outcome `k`: the half-open interval of uniform seeds
`u ∈ [0,1)` that the inverse-transform decoder maps to outcome `k`. -/
def seedSet (k : ℕ) : Set ℝ := Set.Ico (cdf p k) (cdf p (k + 1))















end BookProof.InverseTransform


