-- Prove2me | Definitions.Def_BlockCycleRotation_AllShifts
-- name    : BlockCycleRotation_AllShifts
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:33:43.442714+00:00
-- url     : https://prove2.me/theorems/ae0364eb-af1f-4cdd-9b5d-2b8aa33a6ed2
-- title:
--   BlockCycleRotation: AllShifts definitions
-- statement:
--   Defines the sets of shifts over which the cost is averaged: those the algorithm recurses on ($2k \le n$) and the full range $1 \le k \le n$ used in the remark on all shifts.
--
--   ---
--
--   **The comments in this code predate a citation correction.** They were written against an earlier, incorrect numbering of the source paper; published code is immutable, so they cannot be edited. In this bundle: *Theorem 13* means **Theorem 14**. The numbering used in this description, and in the repository at github.com/dbenbenn/block-cycle-rotation, follows arXiv:2601.00979v1 and is correct.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/AllShifts.lean

-- Generated from BlockCycleRotation/AllShifts.lean by skeleton subtraction (Def bundle).
import Mathlib
/-
# Averaging over all shifts

The remark after Theorem 13.  A run of the Euclidean algorithm on `(n,k)` with
`k` in the upper half first produces the remainder `k` and then repeats the run
of `(n, n-k)`, so

```
remSum n k = k + remSum n (n - k).
```

Summing over `1 ≤ k ≤ n` therefore counts the lower-half remainder sums twice
and adds `∑_{k > n/2} k = 3n²/8 + O(n)`, giving the average

```
(1/n) ∑_{k=1}^{n} remSum n k = (3/8 + 2C)·n + O(n^{1/2+ε}).
```

**Departure from the paper.**  The paper states the reflection for
`n > k ≥ n/2`.  The hypothesis has to be strict: at `2k = n` it would read
`k = k + k`.  Indeed `remSum n (n/2) = n/2` while `k + remSum n (n-k) = n`
there.  The conclusion is unaffected — that single term contributes `O(n)` to a
sum of size `Θ(n²)` — and the proof below uses `n < 2k` throughout.
-/


namespace BlockCycleRotation

open Filter Topology

/-! ## The reflection -/

/-- Shifts in the upper half: `2k > n`. -/
def bigShifts (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun k => ¬ (2 * k ≤ n))

/-- Shifts strictly below the midpoint, `0` included. -/
def smallShifts (n : ℕ) : Finset ℕ := (Finset.range n).filter (fun j => 2 * j < n)







/-! ## The index sets -/









/-! ## Comparing the two lower-half sums

They differ only by the midpoint term `remSum n (n/2)`, present when `n` is
even, which is at most `n`. -/









/-! ## The arithmetic sum `∑_{k > n/2} k` -/







/-! ## The remark -/





end BlockCycleRotation


