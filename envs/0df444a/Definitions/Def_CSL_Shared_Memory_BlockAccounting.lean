-- Prove2me | Definitions.Def_CSL_Shared_Memory_BlockAccounting
-- name    : CSL_Shared_Memory_BlockAccounting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:36.395538+00:00
-- url     : https://prove2.me/theorems/5f0b49ff-d8ba-4e21-aaea-3b3a72ec86b3
-- title:
--   Coded sorting library: Shared / Memory / BlockAccounting
-- statement:
--   Module `CodedSorting.Shared.Memory.BlockAccounting` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # The arithmetic behind the three-block window argument (Section 5.2)
--
--   The head trace below is an integer-valued position function.  Its step
--   bound is explicit, not inferred merely from bijectivity of an address
--   permutation. These lemmas justify window amortization ONCE an actual
--   implementation is proved to have this trace. No implementation is assumed
--   to exist, and no full I/O theorem is asserted here.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.BlockAccounting

import Definitions.Def_CSL_Compat
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The arithmetic behind the three-block window argument (Section 5.2)

The head trace below is an integer-valued position function.  Its step
bound is explicit, not inferred merely from bijectivity of an address
permutation. These lemmas justify window amortization ONCE an actual
implementation is proved to have this trace. No implementation is assumed
to exist, and no full I/O theorem is asserted here.
-/

namespace CSL.BlockAccounting

/-- A head making at most one bit-position move per time step cannot
travel farther than the number of elapsed steps. -/
theorem head_displacement_le_steps (pos : ℕ → ℤ)
    (step : ∀ k, |pos (k + 1) - pos k| ≤ 1) (start count : ℕ) :
    |pos (start + count) - pos start| ≤ (count : ℤ) := by
  induction count with
  | zero => simp
  | succ count ih =>
    calc
      |pos (start + (count + 1)) - pos start| ≤
          |pos (start + count + 1) - pos (start + count)| +
          |pos (start + count) - pos start| := by
            simpa [Nat.add_assoc] using
              (abs_sub_le (pos (start + count + 1)) (pos (start + count)) (pos start))
      _ ≤ 1 + (count : ℤ) := add_le_add (step (start + count)) ih
      _ = ((count + 1 : ℕ) : ℤ) := by push_cast; ring

/-- Immediately after a reset, the head is in the middle block. To leave
the three-block window, it must travel at least one whole block length. -/
theorem exit_three_block_window
    (block center first last : ℤ) (_hblock : 0 < block)
    (hlo : center * block ≤ first) (hhi : first < (center + 1) * block)
    (hout : last < (center - 1) * block ∨ (center + 2) * block ≤ last) :
    block ≤ |last - first| := by
  rcases hout with hleft | hright
  · have hdist : block ≤ first - last := by nlinarith
    calc
      block ≤ first - last := hdist
      _ ≤ |first - last| := le_abs_self _
      _ = |last - first| := abs_sub_comm _ _
  · have hdist : block ≤ last - first := by nlinarith
    exact hdist.trans (le_abs_self _)

/-- Combine the geometric window property with actual head movement. -/
theorem window_exit_needs_block_steps (pos : ℕ → ℤ)
    (step : ∀ k, |pos (k + 1) - pos k| ≤ 1)
    (block center : ℤ) (start count : ℕ) (hblock : 0 < block)
    (hlo : center * block ≤ pos start)
    (hhi : pos start < (center + 1) * block)
    (hout : pos (start + count) < (center - 1) * block ∨
      (center + 2) * block ≤ pos (start + count)) :
    block ≤ (count : ℤ) :=
  (exit_three_block_window block center (pos start) (pos (start + count))
    hblock hlo hhi hout).trans (head_displacement_le_steps pos step start count)

/-- Spaced reset times consume at least `count * block` time steps. -/
theorem spaced_reset_times (time : ℕ → ℕ) (block : ℕ)
    (gap : ∀ i, time i + block ≤ time (i + 1)) (count : ℕ) :
    time 0 + count * block ≤ time count := by
  induction count with
  | zero => simp
  | succ count ih =>
    have h := gap count
    simpa [Nat.succ_mul, Nat.add_assoc] using (Nat.add_le_add_right ih block).trans h

/-- Number of reset intervals is at most the elapsed steps divided by
the block length; this is a finite exact inequality, not big-O notation. -/
theorem reset_count_bound (time : ℕ → ℕ) (block count total : ℕ)
    (hblock : 0 < block)
    (gap : ∀ i, time i + block ≤ time (i + 1))
    (hstop : time count ≤ total) : count ≤ total / block := by
  have h := (spaced_reset_times time block gap count).trans hstop
  apply (Nat.le_div_iff_mul_le hblock).2
  omega

/-- A bounded number of transfers per reset gives the expected block
amortization. Initialization is the additional `1`. -/
theorem transfer_count_bound (time : ℕ → ℕ) (block count total charge transfers : ℕ)
    (hblock : 0 < block)
    (gap : ∀ i, time i + block ≤ time (i + 1))
    (hstop : time count ≤ total)
    (hcharge : transfers ≤ charge * (count + 1)) :
    transfers ≤ charge * (total / block + 1) := by
  exact hcharge.trans (Nat.mul_le_mul_left charge
    (Nat.add_le_add_right (reset_count_bound time block count total hblock gap hstop) 1))

end CSL.BlockAccounting


