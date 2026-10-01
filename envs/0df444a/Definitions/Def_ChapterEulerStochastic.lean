-- Prove2me | Definitions.Def_ChapterEulerStochastic
-- name    : ChapterEulerStochastic
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:54:04.523719+00:00
-- url     : https://prove2.me/theorems/84e2244e-7658-4d31-b2ed-d5940f708535
-- title:
--   Chapter EulerStochastic
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterEulerStochastic.lean`): generated def bundle for ChapterEulerStochastic. See BookProof/ChapterEulerStochastic.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEulerStochastic.lean

import Mathlib


/-!
# Chapter "Wave-function collapse versus Euler's formula", §"Euler's formula for
the probability clock" — the most general probability-preserving linear map on a
2-state phase space

This file formalizes the self-contained mathematical claim of `book.tex`
(§"Euler's formula for the probability clock", line ~3310):

> *"the most general linear transformation of a probability distribution that
> preserves the space of probability distributions is
> `M(a,b) = [[cos²a, cos²b],[sin²a, sin²b]]` … because if we apply `M` to a
> deterministic distribution `(1,0)` or `(0,1)` we must obtain probability
> distributions … the matrix `M` such that `M·½(1,1) = (1,0)` is necessarily
> singular and so it is not suitable to represent a symmetry group."*

The book contrasts this with the rotations `exp(Ja)` that act invertibly on the
wave-function: on the *probability* simplex the only linear symmetries are the
(column-)stochastic matrices, and the specific one collapsing the uniform
distribution to a vertex is singular — motivating the wave-function
parametrization, where the corresponding transformation is an invertible
rotation.

We work over `Matrix (Fin 2) (Fin 2) ℝ`.

* `IsProbVec v` — `v` is a 2-state probability vector (`v i ≥ 0`, `v 0 + v 1 = 1`).
* `PreservesProb M` — `M` maps every probability vector to a probability vector.
* `Mmat a b` — the book's `M(a,b)`.

Results:
* `Mmat_preservesProb` — every `M(a,b)` preserves probability distributions.
* `preservesProb_iff_exists_angles` — **headline**: a linear map preserves the
  space of probability distributions *iff* it is `M(a,b)` for some angles `a,b`
  (the book's "most general" claim).
* `preservesProb_iff_columnStochastic` — the same characterization in terms of
  column-stochasticity (each column is a probability vector).
* `uniform_to_vertex_singular` — **headline**: any probability-preserving `M`
  with `M·½(1,1) = (1,0)` is singular (`M.det = 0`), so it cannot represent a
  symmetry group.
-/

open scoped Matrix BigOperators

namespace BookProof.ChapterEulerStochastic

/-- A 2-state probability vector: non-negative entries summing to `1`. -/
def IsProbVec (v : Fin 2 → ℝ) : Prop := (∀ i, 0 ≤ v i) ∧ v 0 + v 1 = 1

/-- A linear map (matrix) *preserves the space of probability distributions* if
it sends every probability vector to a probability vector. -/
def PreservesProb (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
    ∀ v : Fin 2 → ℝ, IsProbVec v → IsProbVec (M *ᵥ v)

/-- The book's most general probability-preserving matrix
`M(a,b) = [[cos²a, cos²b],[sin²a, sin²b]]`. -/
noncomputable def Mmat (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
    !![Real.cos a ^ 2, Real.cos b ^ 2; Real.sin a ^ 2, Real.sin b ^ 2]

/-
Every probability `p ∈ [0,1]` is realized as `cos² a` for some angle `a`
(with the complementary entry `sin² a = 1 - p`).
-/


/-
The two standard basis / deterministic distributions are probability
vectors.
-/




/-
**Converse direction (constructive):** every `M(a,b)` preserves the space of
probability distributions.
-/


/-
A matrix preserves probability distributions iff it is column-stochastic
(each column is itself a probability vector).
-/


/-
**Headline.** A linear transformation preserves the space of probability
distributions **iff** it equals `M(a,b)` for some real angles `a, b`. This is the
book's claim that `M(a,b)` is the most general probability-preserving linear map
on a 2-state phase space.
-/


/-
**Headline.** The specific probability-preserving matrix that collapses the
uniform distribution `½(1,1)` to the vertex `(1,0)` is singular (`det = 0`), so
it is not suitable to represent a symmetry group.
-/


end BookProof.ChapterEulerStochastic


