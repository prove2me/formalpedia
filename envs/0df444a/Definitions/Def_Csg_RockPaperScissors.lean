-- Prove2me | Definitions.Def_Csg_RockPaperScissors
-- name    : Csg_RockPaperScissors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:42:47.450354+00:00
-- url     : https://prove2.me/theorems/24342887-cd32-46b2-88a4-356488902aa0
-- title:
--   Rock Paper Scissors
-- statement:
--   Definitions and structural lemmas for Rock Paper Scissors, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
namespace Csg.MatrixGame
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I]
  [DecidableEq J] (G : MatrixGame I J)
end Csg.MatrixGame
namespace Csg
inductive RPSAction
  | rock
  | paper
  | scissors
  deriving DecidableEq, Inhabited
instance : Fintype RPSAction where
  elems := {RPSAction.rock, RPSAction.paper, RPSAction.scissors}
  complete := by intro x; cases x <;> decide
inductive RPSState
  | initial
  | win1
  | win2
  | draw
  deriving DecidableEq, Inhabited
instance : Fintype RPSState where
  elems := {RPSState.initial, RPSState.win1, RPSState.win2, RPSState.draw}
  complete := by intro x; cases x <;> decide
def outcome : RPSAction → RPSAction → RPSState
  | .rock, .rock => .draw
  | .rock, .paper => .win2
  | .rock, .scissors => .win1
  | .paper, .rock => .win1
  | .paper, .paper => .draw
  | .paper, .scissors => .win2
  | .scissors, .rock => .win2
  | .scissors, .paper => .win1
  | .scissors, .scissors => .draw
noncomputable def rpsK : RPSState → RPSAction → RPSAction → PMF RPSState
  | .initial, a1, a2 => PMF.pure (outcome a1 a2)
  | .win1, _, _ => PMF.pure .win1
  | .win2, _, _ => PMF.pure .win2
  | .draw, _, _ => PMF.pure .initial
noncomputable def rpsR : RPSState → RPSAction → RPSAction → ℝ := fun _ _ _ => 0
noncomputable def rpsCSG : CSG RPSState RPSAction RPSAction where
  K := rpsK
  r := rpsR
noncomputable def unif3 : RPSAction → ℝ := fun _ => 1 / 3
abbrev rpsGoalWin2 : RPSState → Prop := fun s => s = .win2
end Csg


