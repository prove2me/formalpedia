-- Prove2me | Definitions.Def_TetrisHard_Rows_Reduction
-- name    : TetrisHard_Rows_Reduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T22:52:02.748+00:00
-- url     : https://prove2.me/theorems/4a353b07-1919-4ffa-978b-6f44e741b1cd
-- title:
--   Base board, piece sequence and winning continuations
-- statement:
--   For indexed input P, put H=6T+22. The base board has width 6s+3 and height H+3s+staging. Each bucket occupies six columns: the first two start with four filled bottom cells, the third is empty, the fourth and fifth have holes precisely at one-based rows congruent to 5 modulo 6, and the sixth is full below H. The three-column lock has exactly the three holes and one obstruction described on page 9. The ordered piece list concatenates an initiator I, LG, Sq; aᵢ repetitions of LG, LS, LG, LG, Sq; and two squares for each index, followed by s I pieces, an RG and 3T/2+5 I pieces. The division is exact on normalized inputs. Validity means an actual trajectory sequence clearing H rows; validity of a segment means that a prefix and a winning continuation exist in the original sequence. No canonical-placement conclusion is included in validity. Bucket frames and placement predicates describe the original columns and static walls. A bucket frame retains H=6T+22 for some nonnegative T and at least three staging rows, so every base-orientation spawn lies above the buckets; the source construction supplies these conditions.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, §3, pp. 8–9; §5, pp. 11–12, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Approximation

namespace TetrisHard.Rows

def baseHeight (P : ThreePartition) : ℕ := 6 * P.target + 22

def bucketInitial (x y : ℕ) : Bool :=
  if x % 6 < 2 then decide (y < 4)
  else if x % 6 = 2 then false
  else if x % 6 < 5 then decide ((y + 1) % 6 ≠ 5)
  else true

def baseBoard (P : ThreePartition) (staging : ℕ) : Board where
  height := baseHeight P + 3 * P.s + staging
  width := 6 * P.s + 3
  cell := fun y x =>
    if y.val ≥ baseHeight P then false
    else if x.val < 6 * P.s then bucketInitial x.val y.val
    else if x.val = 6 * P.s then decide (y.val + 2 < baseHeight P)
    else if x.val = 6 * P.s + 1 then decide (y.val + 1 < baseHeight P)
    else decide (y.val + 2 = baseHeight P)

def initiator : List Piece := [.I, .LG, .Sq]
def filler : List Piece := [.LG, .LS, .LG, .LG, .Sq]
def terminator : List Piece := [.Sq, .Sq]

def integerBlock (a : ℕ) : List Piece :=
  initiator ++ (List.replicate a filler).flatten ++ terminator

def numberPieces (P : ThreePartition) : List Piece :=
  (List.ofFn P.entry).flatMap integerBlock

def basePieces (P : ThreePartition) : List Piece :=
  numberPieces P ++ List.replicate P.s .I ++ [.RG] ++
    List.replicate (3 * P.target / 2 + 5) .I

def baseGame (P : ThreePartition) (staging : ℕ) : Game :=
  ⟨baseBoard P staging, basePieces P⟩

/-- A valid complete strategy clears the specified H rows, as in Section 5. -/
def ValidStrategy (R : Rotation) (P : ThreePartition) (staging : ℕ)
    (qs : List PieceState) (B : Board) : Prop :=
  Play R (baseBoard P staging) (basePieces P) qs B (baseHeight P)

/-- The partial segment belongs to an actual winning continuation of the original game.
The segment starts after the prefix `pre`, whose length locates the remaining input. -/
def ValidSegment (R : Rotation) (P : ThreePartition) (staging : ℕ)
    (pre seg : List PieceState) (B B' : Board) : Prop :=
  ∃ v w tail final u,
    Play R (baseBoard P staging) (basePieces P) pre B v ∧
    Play R B ((basePieces P).drop pre.length) seg B' w ∧
    Play R B' ((basePieces P).drop (pre.length + seg.length)) tail final u ∧
    v + w + u = baseHeight P

/-- A common bucket frame before deletions. The source height ends above a complete
notch, and the staging area puts every base-orientation spawn above the buckets.
Interior cells may have been filled by play. -/
def BucketFrame (B : Board) (s H : ℕ) : Prop :=
  B.width = 6 * s + 3 ∧ (∃ T : ℕ, H = 6 * T + 22) ∧ H + 3 ≤ B.height ∧
  ∀ j : Fin s, ∀ y : ℕ, y < H →
    B.occupied (6 * (j.val : ℤ) + 5, y) = true ∧
    ((y + 1) % 6 ≠ 5 →
      B.occupied (6 * (j.val : ℤ) + 3, y) = true ∧
      B.occupied (6 * (j.val : ℤ) + 4, y) = true)

def InBucket (j : ℕ) (q : PieceState) : Prop :=
  ∀ z ∈ q.cells, 6 * (j : ℤ) ≤ z.1 ∧ z.1 < 6 * (j : ℤ) + 6

def InLock (s : ℕ) (q : PieceState) : Prop :=
  ∀ z ∈ q.cells, 6 * (s : ℤ) ≤ z.1 ∧ z.1 < 6 * (s : ℤ) + 3

/-- A bucket is full through the original height (outside sentinels are irrelevant). -/
def BucketFull (B : Board) (j H : ℕ) : Prop :=
  ∀ x ∈ Finset.range 6, ∀ y ∈ Finset.range H,
    B.occupied (6 * (j : ℤ) + x, y) = true

end TetrisHard.Rows


