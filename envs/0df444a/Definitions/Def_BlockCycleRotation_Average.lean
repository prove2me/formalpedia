-- Prove2me | Definitions.Def_BlockCycleRotation_Average
-- name    : BlockCycleRotation_Average
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:42:25.462946+00:00
-- url     : https://prove2.me/theorems/fa68f173-6076-4cf3-ac61-f19e9560e6b3
-- title:
--   Average: The average cost over all shifts
-- statement:
--   Defines $\operatorname{algCost}$ and $\operatorname{avgCost}(n)$, the mean number of moves over the shifts of an array of length $n$ -- the quantity whose asymptotics Theorems 10 and 13 determine.
--
--   ---
--
--   **The comments in this code predate a citation correction.** They were written against an earlier, incorrect numbering of the source paper; published code is immutable, so they cannot be edited. In this bundle: *Observation 6* means **Observation 3**; *Theorem 13* means **Theorem 14**. The numbering used in this description, and in the repository at github.com/dbenbenn/block-cycle-rotation, follows arXiv:2601.00979v1 and is correct.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Average.lean

-- Generated from BlockCycleRotation/Average.lean by skeleton subtraction (Def bundle).
import Definitions.Def_BlockCycleRotation_Algorithm
import Mathlib
/-
# The average cost

Theorem 13 of Blomer--Bux states that the average number of moves, over shifts
`0 ≤ k < n`, is `D * n + O(n^(1/2+ε))` with `D ≈ 1.85`.  This file sets up the
average and proves the unconditional upper bound `avgCost n ≤ 3 * n`, which is
what the worst-case analysis gives.  The content of Theorem 13 is the sharp
constant and the error term; see `ExpSum.lean` for its analytic core.

The algorithm always recurses on the shorter of the two segments, using the
symmetry `M(n,k) = M(n, n-k)`; `algCost` records that.
-/


namespace BlockCycleRotation

open Finset

/-- The number of moves used to rotate `n` items by `k` places.  The algorithm
exploits the symmetry `M(n,k) = M(n, n-k)` and recurses on the shorter segment. -/
def algCost (n k : ℕ) : ℕ := cost n (min k (n - k))





/-- The average number of moves, over all shifts `0 ≤ k < n`. -/
noncomputable def avgCost (n : ℕ) : ℝ := (∑ k ∈ range n, (algCost n k : ℝ)) / n



/-! ## Sanity check

For `n = 21`, `k = 8` the shorter segment is `8`, so this is Observation 6. -/


end BlockCycleRotation


