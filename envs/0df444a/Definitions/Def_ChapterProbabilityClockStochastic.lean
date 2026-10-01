-- Prove2me | Definitions.Def_ChapterProbabilityClockStochastic
-- name    : ChapterProbabilityClockStochastic
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:28:55.795927+00:00
-- url     : https://prove2.me/theorems/002b3416-506a-4a86-a286-75c1e0c17b94
-- title:
--   Chapter ProbabilityClockStochastic
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterProbabilityClockStochastic.lean`): generated def bundle for ChapterProbabilityClockStochastic. See BookProof/ChapterProbabilityClockStochastic.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterProbabilityClockStochastic.lean

import Mathlib


/-!
# Chapter "Wave-function collapse versus Euler's formula", §"Euler's formula for
the probability clock" — stochastic transformations vs. the invertible rotation

Source: `book.tex`, chapter *"Wave-function collapse versus Euler's formula"*,
§*"Euler's formula for the probability clock"* (`book.tex` line ~3320).

After exhibiting the wave-function `Ψ(t) = (cos t, sin t)` and its rotation
`Ψ(t+a) = exp(J a) Ψ(t)`, the book contrasts the *wave-function* picture with a
*direct* linear action on **probability distributions**:

> *"Note that the rotation is an invertible linear transformation that
> preserves the space of wave-functions. This does not happen with probability
> distributions: the most general linear transformation of a probability
> distribution that preserves the space of probability distributions is*
> `M(a,b) = [[cos²a, cos²b], [sin²a, sin²b]]` *… because if we apply `M` to a
> deterministic distribution `[1,0]` or `[0,1]` we must obtain probability
> distributions … the matrix `M` such that `M·(1/2)[1,1]ᵀ = [1,0]ᵀ` is
> necessarily singular and so it is not suitable to represent a symmetry group."*

This file formalizes that self-contained linear-algebra content for the 2-state
phase space.

## Deliverables

* **General form / column-stochastic matrices.**
  * `Mab a b` — the book's matrix `[[cos²a, cos²b], [sin²a, sin²b]]`;
    `Mab_isColumnStochastic` — its columns are probability vectors.
  * `IsColumnStochastic.mulVec_isProbabilityVector` — a column-stochastic matrix
    maps probability vectors to probability vectors.
  * `preserves_prob_iff_isColumnStochastic` — a `2×2` real matrix maps *every*
    probability vector to a probability vector **iff** it is column-stochastic
    (the honest form of "the most general linear transformation preserving the
    space of probability distributions").
  * `isColumnStochastic_eq_Mab` — every column-stochastic `2×2` matrix is
    `Mab a b` for some real `a, b` (so `M(a,b)` really is the general form).

* **The book's singularity point (headline).**
  * `stochastic_uniform_to_deterministic_singular` — if a column-stochastic
    matrix `M` sends the uniform distribution `(1/2, 1/2)` to a deterministic
    distribution `(1, 0)`, then `det M = 0`.
  * `stochastic_uniform_to_deterministic_not_isUnit` — consequently `M` is not
    invertible, hence "not suitable to represent a symmetry group".

* **Contrast: the rotation is a genuine (invertible) symmetry.**
  * `rotMat a` — the rotation `[[cos a, -sin a], [sin a, cos a]]`;
    `rotMat_det` (`= 1`, invertible), `rotMat_isUnit`.
  * `clockPsi` `= (cos t, sin t)` and `rotMat_mulVec_clockPsi`
    (`Ψ(t+a) = rotMat a · Ψ(t)`) — the rotation preserves the wave-function
    circle.
  * `rotMat_eq_exp` — `rotMat a = exp(a·J)` with `J = [[0,-1],[1,0]]`, the
    matrix Euler's formula, and `clockPsi_eq_exp` — `Ψ(t) = exp(t·J)·(1,0)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ProbabilityClockStochastic

open Matrix
open scoped Norms.Operator

/-! ## Probability vectors and column-stochastic matrices -/

/-- A `2`-vector is a probability vector: nonnegative entries summing to `1`. -/
def IsProbabilityVector (v : Fin 2 → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1

/-- A `2×2` matrix is column-stochastic: nonnegative entries, each column
summing to `1` (columns are probability vectors). -/
def IsColumnStochastic (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ ∀ j, ∑ i, M i j = 1

/-- The book's general matrix `M(a,b) = [[cos²a, cos²b], [sin²a, sin²b]]`. -/
noncomputable def Mab (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos a ^ 2, Real.cos b ^ 2; Real.sin a ^ 2, Real.sin b ^ 2]











/-! ## The book's singularity point -/





/-! ## Contrast: the rotation is a genuine invertible symmetry -/

/-- The clock wave-function `Ψ(t) = (cos t, sin t)`. -/
noncomputable def clockPsi (t : ℝ) : Fin 2 → ℝ := ![Real.cos t, Real.sin t]

/-- The generator `J = [[0,-1],[1,0]]` (the "imaginary unit" of the clock). -/
def Jgen : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The rotation matrix `[[cos a, -sin a], [sin a, cos a]]`. -/
noncomputable def rotMat (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos a, -Real.sin a; Real.sin a, Real.cos a]













end BookProof.ProbabilityClockStochastic


