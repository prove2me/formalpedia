-- Prove2me | Definitions.Def_ChapterDensityMarginalConditional
-- name    : ChapterDensityMarginalConditional
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:39:31.586986+00:00
-- url     : https://prove2.me/theorems/35396071-8ccf-48f5-ba3a-033a11337735
-- title:
--   Chapter DensityMarginalConditional
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterDensityMarginalConditional.lean`): generated def bundle for ChapterDensityMarginalConditional. See BookProof/ChapterDensityMarginalConditional.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDensityMarginalConditional.lean

import Mathlib


/-!
# The density matrix: the diagonal is the **marginal**, the unitary is the **conditional**

`BookProof/ChapterDensitySpectral.lean` proves the book's claim (`book.tex`
~1796–1800) that a density matrix is "a diagonal operator rotated by a unitary
operator": `ρ = U · diag(d) · U†` with `d` a probability distribution
(`density_iff_exists_unitary_diagonal`).

The book adds a *probabilistic reading* of the two factors: the diagonal `d`
"defines the marginal probability of the initial state" and the unitary
"defines the conditioned probability of the final state conditioned by the
initial state".  This file supplies exactly that reading, as theorems.

* `bornKernel U i j = ‖U i j‖²` is the Born-rule transition matrix of a unitary.
  It is a genuine conditional probability: nonnegative
  (`bornKernel_nonneg`) with unit row sums (`bornKernel_row_sum`) and unit
  column sums (`bornKernel_col_sum`) — i.e. **doubly stochastic**.
* `density_diag_eq_kernel_apply`: the diagonal of `ρ = U · diag(d) · U†` in the
  computational basis is the transport of `d` by that kernel,
  `ρ i i = ∑ k, ‖U i k‖² · d k`.
* `density_diag_isProbability`: consequently the diagonal of any density matrix
  is itself a probability distribution — the marginal of the final state.
* `density_marginal_conditional`: the headline packaging both halves.

All results are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

namespace BookProof.DensitySpectral

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **Born-rule transition matrix** of a unitary `U`: `bornKernel U i j = ‖U i j‖²`,
the probability of observing the final state `i` given the initial state `j`. -/
def bornKernel (U : Matrix n n ℂ) (i j : n) : ℝ := Complex.normSq (U i j)













end BookProof.DensitySpectral


