-- Prove2me | Definitions.Def_ChapterSpectralGapStability
-- name    : ChapterSpectralGapStability
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:41:00.799638+00:00
-- url     : https://prove2.me/theorems/1cd97f4d-74f4-427c-bbae-b53fe9bef8d0
-- title:
--   Chapter SpectralGapStability
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSpectralGapStability.lean`): generated def bundle for ChapterSpectralGapStability. See BookProof/ChapterSpectralGapStability.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSpectralGapStability.lean

import Mathlib


/-!
# Chapter SpectralGapStability — a spectral gap survives a norm limit

`CONSOLIDATED_PLAN.md` §13.7 records one missing leg of the mass-gap path: the passage
from the truncated Hamiltonian to the continuum needs a *gap-preserving* convergence
statement.  This chapter proves the abstract core of such a statement, for bounded
self-adjoint operators and operator-norm convergence.

The quantitative form of "the operator has a spectral gap at `λ`" used here is
`GapAt A lam d`: `d‖x‖ ≤ ‖Ax − λx‖` for every `x`, i.e. `λ` admits no approximate
eigenvector to accuracy better than `d`.  For a bounded self-adjoint operator this is
exactly `dist(λ, spectrum) ≥ d` — the direction proved below is the one the application
needs: a quantitative gap keeps `λ` out of the spectrum.

## Deliverables

* `GapAt`, `gapAt_perturb` — a quantitative gap degrades by at most the perturbation:
  `GapAt A lam d` and `‖A − B‖ ≤ ε` give `GapAt B lam (d − ε)`.
* `gapAt_of_tendsto` — **a uniform gap survives an operator-norm limit**, with no loss:
  if every `Aₘ` has gap `d` at `λ` and `‖Aₘ − B‖ → 0`, then `B` has gap `d` at `λ`.
* `notMem_spectrum_of_gapAt` — a positive quantitative gap at a real `λ` keeps `λ` out of
  the spectrum of a bounded self-adjoint operator (injectivity from the bound, closed
  range from the same bound, dense range from symmetry) — and its converse
  `exists_gapAt_of_notMem_spectrum`, so the two notions really do agree.
* `notMem_spectrum_of_uniform_gap` and `spectrum_disjoint_of_uniform_window` — the
  gap-preserving conclusion: if the approximants have a uniform gap on an interval and
  converge in operator norm, the limit has no spectrum in that interval.

## Honest boundary

This is a statement about **operator-norm** convergence of *bounded* operators.  The
continuum leg of §13 needs it for the truncation family in the norm-resolvent sense, and
whether the truncations converge that way is exactly the open analytic question; nothing
here asserts that they do.  What the chapter supplies is the implication: *given* such a
convergence, the certified gap of the approximants is inherited by the limit.
-/

noncomputable section

namespace BookProof.SpectralGapStability

open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **A quantitative spectral gap at `λ`**: no vector is moved by less than `d‖x‖` by
`A − λ`.  For a bounded self-adjoint operator this says `dist(λ, spectrum A) ≥ d`. -/
def GapAt (A : F →L[ℂ] F) (lam d : ℝ) : Prop :=
  ∀ x : F, d * ‖x‖ ≤ ‖A x - (lam : ℂ) • x‖















end BookProof.SpectralGapStability


