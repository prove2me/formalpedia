-- Prove2me | Definitions.Def_BlockCycleRotation_ExpSum
-- name    : BlockCycleRotation_ExpSum
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:35:01.234751+00:00
-- url     : https://prove2.me/theorems/623cf391-f238-4f38-b6ac-8767da84cc6b
-- title:
--   ExpSum: The exponential $e(\theta)$ and its elementary estimates
-- statement:
--   Defines $e(\theta) = e^{i\theta}$ and the surrounding notation for the character sums of §4.
--
--   ---
--
--   **The comments in this code predate a citation correction.** They were written against an earlier, incorrect numbering of the source paper; published code is immutable, so they cannot be edited. In this bundle: *Observation 15* means **Observation 17**; *Theorem 13* means **Theorem 14**. The numbering used in this description, and in the repository at github.com/dbenbenn/block-cycle-rotation, follows arXiv:2601.00979v1 and is correct.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/ExpSum.lean

-- Generated from BlockCycleRotation/ExpSum.lean by skeleton subtraction (Def bundle).
import Mathlib
/-
# Elementary bounds on exponential sums

This file formalises Observation 15 of

  Valentin Blomer and Kai-Uwe Bux,
  *The cost of cyclic permutations and remainder sums in the Euclidean algorithm*,
  AofA 2026.  arXiv:2601.00979.

Observation 15 is the *only* analytic input to the error term in Theorem 13.
Notably it needs no Kloosterman or Weil bounds: everything follows from Jordan's
inequality (`Real.mul_abs_le_abs_sin` in Mathlib) together with the closed form
of a geometric series, i.e. the trivial bound on an exponential sum, with no
square-root cancellation anywhere.

The two estimates proved here are, for `0 < |θ| ≤ π`:

* `‖∑ j ∈ Ico B T, e(jθ)‖ ≤ π / |θ|`, and
* `‖∑ j ∈ Ico 1 T, j * e(jθ)‖ ≤ (T - 1) * (π / |θ|)`,

the second by writing `j` as a count and swapping the order of summation, which
is the double-counting argument in the paper.
-/


open Real Finset

namespace BlockCycleRotation

/-- `e θ` is the point `exp (θ i)` on the unit circle. -/
noncomputable def e (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

















/-! ## The exponential sum bounds -/









/-! ### The sharp form of Observation 15

The paper does not stop at the triangle inequality: after the double-counting
step it evaluates the inner geometric sums in closed form,

  `∑_{1≤j<T} j x^j = ((T-1) x^T - (x^T - x)/(x-1)) / (x-1)`,

and reads off `π²/(2θ²) + (T-1)π/(2|θ|)`.  That is the bound stated in the
paper, and it is what we prove here. -/





end BlockCycleRotation


