-- Prove2me | Definitions.Def_MahjongSolitaire_Stacks_OperationalModel
-- name    : MahjongSolitaire_Stacks_OperationalModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:15:46.303822+00:00
-- url     : https://prove2.me/theorems/720cea1e-320b-4745-82f0-fa6b5a4813b7
-- title:
--   Isolated-stack Mahjong states and simultaneous legal play
-- statement:
--   A state is a finite ordered list of stacks, each a finite list of natural-number group labels written from top to bottom. Positions in a stack distinguish tiles even when their labels agree. The outer list retains stack identities, including empty stacks.
--
--   For indices i and j, a move is defined only when the indices are distinct, both stacks exist and are nonempty, and their exposed top labels agree. It removes exactly the head of each selected stack. Both labels are inspected in the state before either removal. Every other stack is unchanged. A missing stack, an empty stack, unequal labels, or coincident indices makes the attempted move fail.
--
--   A state is cleared when every stack is empty. It is solvable when a finite sequence of legal moves, possibly empty, reaches a cleared state. These operational definitions do not impose initial shape or multiplicity restrictions and do not assume a solver, a reduction, or a winning strategy. Isolated geometry makes every exposed top tile playable; no side obstruction needs additional data.
-- source:
--   Michiel de Bondt, Solving Mahjong Solitaire boards with peeking, arXiv:1203.6559v1, Theorem 3, p. 2; rules pp. 1–2; proof pp. 2–5. https://arxiv.org/abs/1203.6559v1

import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

namespace MahjongSolitaire.Stacks

/-- Stack positions retain their identities; each inner list is top-to-bottom. -/
abbrev State := List (List Nat)

/-- Remove two equal exposed tiles in distinct stacks, inspecting both old heads. -/
def play (S : State) (i j : Nat) : Option State :=
  match S[i]?, S[j]? with
  | some (a :: xs), some (b :: ys) =>
      if i ≠ j ∧ a = b then some ((S.set i xs).set j ys) else none
  | _, _ => none

/-- One simultaneous matching-pair removal. -/
def LegalMove (S T : State) : Prop :=
  ∃ i j : Nat, play S i j = some T

/-- Every stack is empty, including the case of no stacks. -/
def IsCleared (S : State) : Prop :=
  ∀ stack ∈ S, stack = []

/-- A finite legal play clears the board; a play may contain zero moves. -/
def Solvable (S : State) : Prop :=
  ∃ T : State, Relation.ReflTransGen LegalMove S T ∧ IsCleared T

end MahjongSolitaire.Stacks


