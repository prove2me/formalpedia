-- Prove2me | Definitions.Def_TetrisHard_Rows_Reservoir
-- name    : TetrisHard_Rows_Reservoir
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T22:55:34.568014+00:00
-- url     : https://prove2.me/theorems/7f2efb6e-f902-4133-8963-6b81a85614ac
-- title:
--   Two-lock reservoir construction and allocation bookkeeping
-- statement:
--   The extended board has width 6s+7. Below the old board lie two lock rows and r reservoir rows. The reservoir is filled only in its first column. Of the four new columns, the first is full in both lock rows; the second is empty in both; the third and fourth are empty only in the upper lock row. This is the four-cell RG opening in Figure 9(b). Four filled columns extend the old occupied rows on the right; the staging rows above remain empty as drawn in the figure. The sequence appends one RG and r(6s+6)/4 squares; even r ensures divisibility. The module also counts empty bucket cells and expresses both allocation clauses through a pre-key board and the final cleared board, preserving row compression rather than tracking stale coordinates.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, §6.2, pp. 20–21, Figure 9(b); Corollary 5.6, p. 12, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reasonable

namespace TetrisHard.Rows

/-- Figure 9(b). The staging area drawn above the old board is empty, including
above the four added columns. The two lock rows have the actual four-cell RG opening. -/
def reservoirBoard (P : ThreePartition) (staging r : ℕ) : Board where
  height := (baseBoard P staging).height + 2 + r
  width := 6 * P.s + 7
  cell := fun y x =>
    if y.val < r then decide (x.val = 0)
    else if y.val = r then decide (x.val ≠ 6 * P.s + 4)
    else if y.val = r + 1 then decide (x.val < 6 * P.s + 4)
    else if x.val < 6 * P.s + 3 then
      (baseBoard P staging).occupied (x.val, (y.val : ℤ) - r - 2)
    else decide (y.val < r + 2 + baseHeight P)

def reservoirGame (P : ThreePartition) (staging r : ℕ) : Game :=
  {board := reservoirBoard P staging r,
   pieces := basePieces P ++ [.RG] ++ List.replicate (r * (6 * P.s + 6) / 4) .Sq}

/-- Finite count of original bucket cells still empty. -/
def emptyBucketCells (B : Board) (j H : ℕ) : ℕ :=
  ((Finset.range 6 ×ˢ Finset.range H).filter fun z =>
    B.occupied (6 * (j : ℤ) + z.1, z.2) = false).card

/-- The complete allocation assertion tracks the pre-key board and the final board,
so lock cells are counted through row compression rather than by stale coordinates. -/
def BucketLockAllocation (R : Rotation) (P : ThreePartition) (staging : ℕ)
    (qs : List PieceState) (final : Board) : Prop :=
  let cut := (numberPieces P).length + P.s
  (∀ q ∈ qs.take cut, ∃ j : Fin P.s, InBucket j.val q) ∧
  (∃ mid, Play R (baseBoard P staging) (basePieces P) (qs.take cut) mid 0 ∧
    ∀ j : Fin P.s, BucketFull mid j.val (baseHeight P)) ∧
  (∀ q ∈ qs.drop cut, InLock P.s q) ∧ final.Empty

end TetrisHard.Rows


