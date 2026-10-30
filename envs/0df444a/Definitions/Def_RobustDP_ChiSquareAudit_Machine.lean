-- Prove2me | Definitions.Def_RobustDP_ChiSquareAudit_Machine
-- name    : RobustDP_ChiSquareAudit_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:42:47.385755+00:00
-- url     : https://prove2.me/theorems/97d4c1e0-fa20-42ae-8399-3ad541986b9f
-- title:
--   Counted exact-real primitives and comparison mergesort
-- statement:
--   A computation returns its value and its natural-number operation count; sequencing adds the counts of the executed computations. Real addition, subtraction, multiplication and comparison cost one operation. Guarded division costs at most two, and guarded nonnegative square root at most two. A rejected zero divisor or negative radicand returns zero after its charged guard. These rejection branches do not replace any valid root or variance case in the program.
--
--   Input-coordinate reads cost one. Fixed blocks of structural work charge the displayed number of unit operations, including record reads, list constructors, branches, array writes, index changes and loop control. The natural counter itself is metalevel accounting. Rows retain a value, its weight and its original coordinate. Cells store the two adjacent values and the three moments. Results store the selected threshold, value and constructed multiplier array.
--
--   Sorting is an actual recursive alternating split followed by comparison merging; it is never an oracle primitive. Dimension fuel bounds recursion and is sufficient on every list produced by the support pass. The logarithmic factor is $\lceil\log_2(n+1)\rceil$ using the natural ceiling logarithm. This is an exact-real arithmetic model, with constant-time reads and growable-array writes, rather than a claim about rational bit complexity or Lean evaluator time.
-- source:
--   G. Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07, revised May 4, 2004, p. 19, Section 4.2, sorting and arithmetic-work interpretation of the complexity sentence

import Mathlib

namespace RobustDP.ChiSquareAudit

/-- Writer semantics: every primitive returns its result together with its charge.
The counter is accumulated only by sequencing these actual computations. -/
structure Run (α : Type) where
  value : α
  steps : ℕ

instance : Monad Run where
  pure x := ⟨x, 0⟩
  bind x f := let y := f x.value; ⟨y.value, x.steps + y.steps⟩

/-- One primitive structural operation (read/write, constructor, branch, loop or index).
Several consecutive structural operations are explicitly bundled with `overhead`. -/
def overhead (n : ℕ) : Run Unit := ⟨(), n⟩

def radd (x y : ℝ) : Run ℝ := ⟨x + y, 1⟩
def rsub (x y : ℝ) : Run ℝ := ⟨x - y, 1⟩
def rmul (x y : ℝ) : Run ℝ := ⟨x * y, 1⟩

/-- Guard is charged. The zero branch never performs a division. -/
noncomputable def rdiv (x y : ℝ) : Run ℝ := by
  classical
  exact if y = 0 then ⟨0, 1⟩ else ⟨x / y, 2⟩

/-- Guard is charged. All calls used for valid data have nonnegative radicands. -/
noncomputable def rsqrt (x : ℝ) : Run ℝ := by
  classical
  exact if x < 0 then ⟨0, 1⟩ else ⟨Real.sqrt x, 2⟩

noncomputable def rle (x y : ℝ) : Run Bool := by
  classical
  exact ⟨decide (x ≤ y), 1⟩

noncomputable def rlt (x y : ℝ) : Run Bool := by
  classical
  exact ⟨decide (x < y), 1⟩

noncomputable def req (x y : ℝ) : Run Bool := by
  classical
  exact ⟨decide (x = y), 1⟩

def inputRead {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : Run ℝ := ⟨x i, 1⟩

structure Row where
  v : ℝ
  q : ℝ
  original : ℕ
  deriving Inhabited

structure Cell where
  low : ℝ
  high : Option ℝ
  a : ℝ
  b : ℝ
  c : ℝ
  deriving Inhabited

structure Best where
  alpha : ℝ
  val : ℝ
  deriving Inhabited

structure Answer where
  best : Best
  multiplier : Array ℝ

/-- A structural alternating split: no sort primitive is hidden here. -/
def splitRows : List Row → Run (List Row × List Row)
  | [] => ⟨([], []), 2⟩
  | [x] => ⟨([x], []), 4⟩
  | x :: y :: xs => do
    overhead 8
    let p ← splitRows xs
    pure (x :: p.1, y :: p.2)

/-- At most one real comparison per emitted element. Empty tails are shared. -/
noncomputable def mergeRows : ℕ → List Row → List Row → Run (List Row)
  | 0, _, _ => ⟨[], 2⟩
  | _ + 1, [], ys => ⟨ys, 3⟩
  | _ + 1, xs, [] => ⟨xs, 3⟩
  | fuel + 1, x :: xs, y :: ys => do
    overhead 8
    let takeLeft ← rle x.v y.v
    if takeLeft then
      let tail ← mergeRows fuel xs (y :: ys)
      pure (x :: tail)
    else
      let tail ← mergeRows fuel (x :: xs) ys
      pure (y :: tail)

/-- Top-down mergesort. Fuel n suffices for every input list of length at most n. -/
noncomputable def sortRows : ℕ → List Row → Run (List Row)
  | 0, xs => ⟨xs, 2⟩
  | _ + 1, [] => ⟨[], 3⟩
  | _ + 1, [x] => ⟨[x], 4⟩
  | fuel + 1, x :: y :: xs => do
    overhead 8
    let halves ← splitRows (x :: y :: xs)
    let left ← sortRows fuel halves.1
    let right ← sortRows fuel halves.2
    mergeRows (fuel + 1) left right

/-- A counted bound for the logarithmic number of split levels. -/
def sortingLevels (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

end RobustDP.ChiSquareAudit


