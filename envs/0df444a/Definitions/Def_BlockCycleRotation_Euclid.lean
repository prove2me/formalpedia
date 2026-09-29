-- Prove2me | Definitions.Def_BlockCycleRotation_Euclid
-- name    : BlockCycleRotation_Euclid
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:35:11.656143+00:00
-- url     : https://prove2.me/theorems/ace9599f-263a-4f68-9f23-cee090230b9d
-- title:
--   Euclid: Remainder sums in the Euclidean algorithm
-- statement:
--   Defines $\operatorname{remSum}(n,k)$, the sum of the remainders produced by the Euclidean algorithm on the pair $(n,k)$, and $\operatorname{moveCount}(n,k) = n - \gcd(n,k) + 2\operatorname{remSum}(n,k)$, the move count of the block cycle rotation. These are the two arithmetic quantities the whole development is about.
--
--   ---
--
--   **The comments in this code predate a citation correction.** They were written against an earlier, incorrect numbering of the source paper; published code is immutable, so they cannot be edited. In this bundle: *Lemma 12* means **Lemma 11**; *Observation 6* means **Observation 3**; *equation (12)* means **Lemma 11(2) with equation (7)**. The numbering used in this description, and in the repository at github.com/dbenbenn/block-cycle-rotation, follows arXiv:2601.00979v1 and is correct.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Euclid.lean

-- Generated from BlockCycleRotation/Euclid.lean by skeleton subtraction (Def bundle).
import Mathlib
/-
# Remainder sums in the Euclidean algorithm

This file formalises the arithmetic core of

  Valentin Blomer and Kai-Uwe Bux,
  *The cost of cyclic permutations and remainder sums in the Euclidean algorithm*,
  AofA 2026, LIPIcs vol. 381, 14:1--14:17.  arXiv:2601.00979.

The block cycle rotation algorithm rotates an array of length `n` by `k` places.
By Lemma 12 of the paper, the sequence of segment lengths arising in its
recursion is exactly the sequence of remainders produced by the Euclidean
algorithm on `(n, k)`, and the total number of moves is

  `moveCount n k = n - gcd n k + 2 * remSum n k`.

Here we define `remSum`, the sum of those remainders, and prove the worst-case
bound underlying Theorem A: the algorithm uses at most `3 * (n - gcd n k)` moves.
-/


namespace BlockCycleRotation

/-! ## The remainder sum -/

/-- `remSum n k` is the sum of the nonzero remainders produced by the Euclidean
algorithm started on the pair `(n, k)`.

Concretely, with `r₁ = k`, `p₁ = n` and `rᵢ₊₁ = pᵢ % rᵢ`, `pᵢ₊₁ = rᵢ`, this is
`r₁ + r₂ + ⋯`, the sum stopping at the last nonzero remainder.  This is the
quantity denoted `𝔯₁ + 𝔯₂ + ⋯` in Lemma 12 of the paper. -/
def remSum (n k : ℕ) : ℕ :=
  if h : k = 0 then 0 else k + remSum k (n % k)
termination_by k
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)





/-! ## The master inequality

The bound we ultimately want, `remSum n k + gcd n k ≤ n` for `2 * k ≤ n`, is not
directly amenable to induction: the hypothesis `2 * k ≤ n` is *not* inherited by
the recursive call.  (For `n = 21`, `k = 8` the algorithm steps to `(8, 5)`, and
`2 * 5 > 8`.)  The following inequality holds for *every* pair and does
propagate, and it specialises to the bound we want. -/



/-! ## The worst-case bound (Theorem A, worst case) -/



/-! ## Scaling

Running the Euclidean algorithm on `(d·n, d·k)` is running it on `(n, k)` with
every remainder multiplied by `d`.  This is what lets the coprime form of the
Heilbronn identity be aggregated over `d = gcd(n, k)`. -/



/-! ## Move count -/

/-- The number of moves the block cycle algorithm performs when rotating an
array of length `n` by `k ≤ n / 2` places (equation (12) of the paper):
`n - gcd n k` moves of type B, and `2 * remSum n k` moves of type A. -/
def moveCount (n k : ℕ) : ℕ := n - Nat.gcd n k + 2 * remSum n k





/-! ## Sanity checks against the paper

Observation 6 of the paper works out the example of a left segment of length `8`
and a right segment of length `13`, i.e. `n = 21`, `k = 8`, and reports a cost of
`58` moves, via the remainder sequence `8, 5, 3, 2, 1`. -/

-- `remSum` is defined by well-founded recursion, so `decide` cannot reduce it;
-- `#guard` evaluates via the interpreter and fails at elaboration time if false.

end BlockCycleRotation


