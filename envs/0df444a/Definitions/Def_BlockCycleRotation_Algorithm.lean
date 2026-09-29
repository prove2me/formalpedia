-- Prove2me | Definitions.Def_BlockCycleRotation_Algorithm
-- name    : BlockCycleRotation_Algorithm
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:25:11.510687+00:00
-- url     : https://prove2.me/theorems/5c2c52fc-50fe-4bd8-9b6a-6d470cf86b45
-- title:
--   BlockCycleRotation: Algorithm definitions
-- statement:
--   Defines the block cycle algorithm's cost recursion $\operatorname{cost}(n,k)$ and the terminal segment $\operatorname{finalSeg}(n,k)$, following §2 of Blomer--Bux. Lemma 11 identifies these with the Euclidean quantities of the previous bundle.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Algorithm.lean

-- Generated from BlockCycleRotation/Algorithm.lean by skeleton subtraction (Def bundle).
import Mathlib
/-
# The block cycle recursion and its move count

This file formalises the cost accounting of section 2 and Lemma 12 of

  Valentin Blomer and Kai-Uwe Bux,
  *The cost of cyclic permutations and remainder sums in the Euclidean algorithm*,
  AofA 2026, LIPIcs vol. 381, 14:1--14:17.  arXiv:2601.00979.

The block cycle algorithm, rotating an array of length `n` by `k` places,
recurses on the pair `(n, k)`.  Writing `b = ⌊n / k⌋` for the number of blocks,
one step performs a cyclic permutation of `b` blocks of length `k`, costing
`(b + 1) * k` moves, and leaves the subproblem of rotating the last
`k + (n % k)` entries by `n % k`.  So the algorithm's recursion is

  `(n, k) ↦ (k + n % k, n % k)`.

Note this is *not* the Euclidean step `(n, k) ↦ (k, n % k)`: the first components
differ.  They agree modulo the second component, which is the congruence
`pᵢ ≡ nᵢ mod 𝔯ᵢ` appearing in the paper's proof of Lemma 12, and it is why the
segment lengths are nevertheless the Euclidean remainders.

The main result is `cost_add_gcd`, an unconditional form of the paper's
equation (12):

  `cost n k + gcd n k = n + 2 * remSum n k`,

which identifies the algorithm's true move count with the quantity `moveCount`
studied in `Euclid.lean`.  Combined with the worst-case bound proved there, this
upgrades that bound from a statement about a recurrence to a statement about the
number of moves the algorithm actually performs.
-/


namespace BlockCycleRotation

/-! ## The algorithm's recursion -/

/-- `cost n k` is the total number of moves the block cycle algorithm performs
when rotating an array of length `n` by `k` places.

One step permutes `⌊n / k⌋` blocks of length `k` cyclically, at a cost of
`(⌊n / k⌋ + 1) * k` moves, and recurses on `(k + n % k, n % k)`. -/
def cost (n k : ℕ) : ℕ :=
  if h : k = 0 then 0 else (n / k + 1) * k + cost (k + n % k) (n % k)
termination_by k
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)





/-- `finalSeg n k` is the segment length the recursion terminates on. -/
def finalSeg (n k : ℕ) : ℕ :=
  if h : k = 0 then n else finalSeg (k + n % k) (n % k)
termination_by k
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)





/-! ## Arithmetic of one step -/









/-! ## Lemma 12(1): where the recursion stops -/



/-! ## Equation (12): the move count -/









/-! ## Sanity checks

Observation 6: `n = 21`, `k = 8` costs 58 moves.  The recursion visits
`(21,8), (13,5), (8,3), (5,2), (3,1)` at costs `24, 15, 9, 6, 4`. -/


/-! ## The Fibonacci worst case

Observation 6 says the worst case is approached along `k = F_m`, `n = F_{m+2}`,
where the algorithm takes `3∑_{j≤m} F_j - 2 = 3n - 3gcd(n,k) - 2` moves.  Since
`∑_{j≤m} F_j = F_{m+2} - 1` and `gcd(F_{m+2}, F_m) = 1`, that is `3n - 5`. -/













end BlockCycleRotation


