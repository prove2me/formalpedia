-- Prove2me | Definitions.Def_TetrisHard_Rows_Approximation
-- name    : TetrisHard_Rows_Approximation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T22:51:10.561479+00:00
-- url     : https://prove2.me/theorems/991c2ec7-1692-440e-8d3f-2fccfef33571
-- title:
--   Explicit game encodings and cleared-row approximation
-- statement:
--   A game code consists of unary dimensions, every board cell, the piece-list length and the ordered piece types. A proposed row count is encoded in unary. For a nonempty list of p pieces, an ε-approximation answer is an attainable count v such that every attainable count w satisfies w ≤ p^(1−ε)v. Comparing with every attainable count expresses the actual optimum without taking an empty or unbounded supremum. For an empty piece list, the answer is zero. The valid-query set includes all legal initial boards and all finite piece lists, including small boards on which spawning is blocked. The resulting relation is a concrete instance of the independent search-problem definition.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, §2, pp. 4–7; Theorem 6.5, p. 21, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Game
import Definitions.Def_TetrisHard_Rows_ThreePartition
import Definitions.Def_TetrisHard_Rows_Search

namespace TetrisHard.Rows

def Piece.code : Piece → ℕ
  | .Sq => 0 | .LG => 1 | .RG => 2 | .LS => 3 | .RS => 4 | .I => 5 | .T => 6

/-- Dimensions, explicit occupancy, length and ordered types. The dimensions and list
length delimit the occupancy and piece fields, including empty sequences. -/
def Game.code (G : Game) : List Bool :=
  unaryCode [G.board.height, G.board.width] ++ G.board.rows.flatten ++
    unaryCode (G.pieces.length :: G.pieces.map Piece.code)

/-- Feasible count with the full factor measured in pieces. Comparing with every
attainable score expresses the true maximum without a totalized supremum. -/
def RowApproximation (R : Rotation) (ε : ℝ) (G : Game) (v : ℕ) : Prop :=
  Attainable R G v ∧
    if G.pieces = [] then v = 0 else
      ∀ w, Attainable R G w → (w : ℝ) ≤ (G.pieces.length : ℝ) ^ (1 - ε) * v

def rowSearch (R : Rotation) (ε : ℝ) : SearchProblem where
  valid := fun x => ∃ G : Game, G.Legal ∧ x = G.code
  answer := fun x y => ∃ (G : Game) (v : ℕ),
    G.Legal ∧ x = G.code ∧ y = unaryCode [v] ∧ RowApproximation R ε G v

end TetrisHard.Rows


