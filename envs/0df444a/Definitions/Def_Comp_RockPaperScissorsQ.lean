-- Prove2me | Definitions.Def_Comp_RockPaperScissorsQ
-- name    : Comp_RockPaperScissorsQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:46:51.401346+00:00
-- url     : https://prove2.me/theorems/f08c05d7-d616-4123-a531-349154909947
-- title:
--   Rock Paper Scissors Q
-- statement:
--   Definitions and structural lemmas for Rock Paper Scissors Q, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/RockPaperScissorsQ.lean

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
set_option linter.hashCommand false
namespace Comp
open Csg
def rpsActions : List RPSAction := [.rock, .paper, .scissors]
def rpsPayoffQ : RPSAction → RPSAction → ℚ
  | .rock, .rock => 0
  | .rock, .paper => 1
  | .rock, .scissors => -1
  | .paper, .rock => -1
  | .paper, .paper => 0
  | .paper, .scissors => 1
  | .scissors, .rock => 1
  | .scissors, .paper => -1
  | .scissors, .scissors => 0
def rpsMatrixQ : MatrixGameQ RPSAction RPSAction where
  A := rpsPayoffQ
def rpsUnif : RPSAction → ℚ := fun _ => 1 / 3
def mpActions : List Bool := [true, false]
def mpPayoffQ : Bool → Bool → ℚ
  | true, true => -1
  | true, false => 1
  | false, true => 1
  | false, false => -1
def mpMatrixQ : MatrixGameQ Bool Bool where
  A := mpPayoffQ
def mpUnif : Bool → ℚ := fun _ => 1 / 2
end Comp


