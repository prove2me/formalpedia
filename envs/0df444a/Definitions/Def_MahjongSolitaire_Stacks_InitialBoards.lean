-- Prove2me | Definitions.Def_MahjongSolitaire_Stacks_InitialBoards
-- name    : MahjongSolitaire_Stacks_InitialBoards
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:16:01.990802+00:00
-- url     : https://prove2.me/theorems/9a6d600b-4a0a-413a-a072-42096c0df0ae
-- title:
--   Initial three-tile shapes and four copies per group
-- statement:
--   A board consists of a natural number g of groups and a finite ordered list of stacks. It is a valid initial board exactly when every stack has three tiles of the form [a,a,b] or [a,b,b] from top to bottom, every label is below g, and each label in {0,...,g−1} occurs exactly four times in the entire board.
--
--   The schematic labels a and b are chosen independently for each stack and are allowed to coincide, since the printed diagrams do not specify an inequality. Tile occurrences retain distinct positions even when their labels coincide. Neither g nor the number of stacks has a fixed upper bound. The board with g=0 and no stacks is valid. Shape and four-copy conditions apply only initially; subsequent play uses the unrestricted operational state type.
-- source:
--   Michiel de Bondt, Solving Mahjong Solitaire boards with peeking, arXiv:1203.6559v1, Theorem 3, p. 2; rules pp. 1–2; proof pp. 2–5. https://arxiv.org/abs/1203.6559v1

import Definitions.Def_MahjongSolitaire_Stacks_OperationalModel

namespace MahjongSolitaire.Stacks

/-- Input data; validity is a separate predicate, not a bundled solvability condition. -/
structure Board where
  groupCount : Nat
  stacks : State
  deriving DecidableEq, Repr

/-- Exactly three tiles with equal top two or equal bottom two. -/
def allowedShape : List Nat → Bool
  | [a, b, c] => (a == b) || (b == c)
  | _ => false

/-- Initial shape, label-range, and global four-copy conditions. -/
def validInitial (B : Board) : Bool :=
  B.stacks.all allowedShape &&
  B.stacks.flatten.all (fun a => a < B.groupCount) &&
  (List.range B.groupCount).all (fun a => B.stacks.flatten.count a == 4)

/-- The exact restricted input class; intermediate states need not satisfy it. -/
def IsValidInitial (B : Board) : Prop := validInitial B = true

end MahjongSolitaire.Stacks


