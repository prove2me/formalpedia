-- Prove2me | Definitions.Def_BlockCycleRotation_Rotate
-- name    : BlockCycleRotation_Rotate
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:35:20.2846+00:00
-- url     : https://prove2.me/theorems/6f81f805-fd4b-4690-a03a-3673dbe4a458
-- title:
--   Rotate: The block cycle algorithm on lists
-- statement:
--   Defines $\operatorname{bcRotate}$, the block cycle rotation as an operation on lists, so that its correctness against `List.rotate` can be stated and proved.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Rotate.lean

-- Generated from BlockCycleRotation/Rotate.lean by skeleton subtraction (Def bundle).
import Mathlib
/-
# Correctness of the block cycle step

The block cycle algorithm rotates a list `l` of length `n` left by `k`.  Writing
`b = ⌊n / k⌋`, one step cyclically permutes the first `b` blocks of length `k`,
moving block 1 to the end of that group.  This file proves that step correct:
the first `(b - 1) * k` entries land in their final position, and what remains is
a rotation of the last `k + (n % k)` entries.

Reference: Blomer--Bux, section 2 and Figure 1.
-/


namespace BlockCycleRotation

variable {α : Type*}



/-! ## The algorithm

The step above is degenerate when `⌊n / k⌋ = 1`, i.e. when `k > n / 2`: it moves
nothing and recurses on the whole list.  This is exactly the case the paper
handles "using symmetry", by swapping the roles of the two segments and moving
blocks the other way.  We implement that mirrored step by reversal, which turns
a left rotation by `k` into a left rotation by `n - k` (`List.reverse_rotate`).

Termination is lexicographic in `(k, l.length)`: the left step keeps `k` and
shortens the list, the mirrored step strictly decreases `k`. -/

/-- The block cycle rotation algorithm on lists. -/
def bcRotate (l : List α) (k : ℕ) : List α :=
  if k = 0 then l
  else if l.length ≤ k then l
  else if 2 * k ≤ l.length then
    (l.take (l.length / k * k)).drop k ++
      bcRotate ((l.take (l.length / k * k)).take k ++ l.drop (l.length / k * k)) k
  else
    (bcRotate l.reverse (l.length - k)).reverse
termination_by (k, l.length)
decreasing_by
  · -- left step: `k` unchanged, the list gets strictly shorter
    refine Prod.Lex.right _ ?_
    have hk : 0 < k := Nat.pos_of_ne_zero ‹k ≠ 0›
    have hb : 2 ≤ l.length / k := (Nat.le_div_iff_mul_le hk).2 (by omega)
    have hmn : l.length / k * k ≤ l.length := Nat.div_mul_le_self _ _
    have hkm : 2 * k ≤ l.length / k * k := by
      calc 2 * k = 2 * k := rfl
        _ ≤ l.length / k * k := Nat.mul_le_mul_right k hb
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · -- mirrored step: `k` strictly decreases
    exact Prod.Lex.left _ _ (by omega)



/-! ## Sanity checks -/




end BlockCycleRotation


