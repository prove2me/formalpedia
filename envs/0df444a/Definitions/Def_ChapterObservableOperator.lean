-- Prove2me | Definitions.Def_ChapterObservableOperator
-- name    : ChapterObservableOperator
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:22:21.971639+00:00
-- url     : https://prove2.me/theorems/014f1e08-8731-4bed-940e-579b59100428
-- title:
--   Chapter ObservableOperator
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterObservableOperator.lean`): generated def bundle for ChapterObservableOperator. See BookProof/ChapterObservableOperator.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterObservableOperator.lean

import Definitions.Def_ChapterObservableExpectation
import Mathlib


/-!
# Chapter "The Coherent State of Attention", §"The Posterior: Observable
Operators and Expectation Values" — the observable as an **operator**

`BookProof.ChapterObservableExpectation` proves the expectation-value identity
using only the *spectral data* of the observable (its eigenvalues `vⱼ` indexed by
the outcomes) and records the disparity with the informal chapter, which writes
the observable as the operator

  `V̂ = ∑ⱼ vⱼ |kⱼ⟩⟨kⱼ|`

and appeals to the spectral theorem.  This module closes that disparity by
building the operator itself, in finite dimensions, as a matrix:

* `outerProj k` — the rank-one operator `|k⟩⟨k|`;
* `observableOp k v` — the observable `V̂ = ∑ⱼ vⱼ |kⱼ⟩⟨kⱼ|` with real eigenvalues;
* `observableOp_isHermitian` — **`V̂` is Hermitian** (a genuine observable);
* `bornProb` — the Born statistics `pⱼ = |⟨kⱼ|q⟩|²` of measuring `V̂` in the state
  `|q⟩`, with `bornProb_nonneg` and (for an orthonormal eigenbasis and a unit
  state) `bornProb_sum_one`;
* `expectation_outerProj`, **`observableOp_expectation`** — the operator
  expectation `⟨q|V̂|q⟩` is the Born-weighted sum `∑ⱼ pⱼ vⱼ` of the eigenvalues,
  i.e. exactly `ChapterObservableExpectation.observableExpectation`;
* `observableOp_expectation_mem_convexHull` — hence, for an orthonormal
  eigenbasis and a unit state, the expectation lies in the convex hull of the
  eigenvalues;
* `observableOp_expectation_real` — the expectation of a Hermitian observable is
  real.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterObservableOperator

variable {n m : ℕ}

/-! ## The observable operator -/

/-- The rank-one operator `|k⟩⟨k|`, as a matrix. -/
def outerProj (k : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => k a * (starRingEnd ℂ) (k b)

/-- The **observable** `V̂ = ∑ⱼ vⱼ |kⱼ⟩⟨kⱼ|` with eigenvectors `kⱼ` and real
eigenvalues `vⱼ`. -/
def observableOp (k : Fin m → EuclideanSpace ℂ (Fin n)) (v : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ j, (v j : ℂ) • outerProj (k j)





/-! ## Expectation values -/

/-- The **expectation value** `⟨q| A |q⟩` of a matrix observable in the state
`|q⟩`. -/
def expectation (A : Matrix (Fin n) (Fin n) ℂ) (q : EuclideanSpace ℂ (Fin n)) : ℂ :=
  ∑ a, ∑ b, (starRingEnd ℂ) (q a) * A a b * q b

/-- The **Born probability** of the outcome `j`: `pⱼ = |⟨kⱼ|q⟩|²`. -/
def bornProb (k : Fin m → EuclideanSpace ℂ (Fin n)) (q : EuclideanSpace ℂ (Fin n))
    (j : Fin m) : ℝ := ‖(inner ℂ (k j) q : ℂ)‖ ^ 2









/-! ## An orthonormal eigenbasis makes the Born statistics a probability law -/







end BookProof.ChapterObservableOperator

end


