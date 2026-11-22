-- Prove2me | Definitions.Def_Csg_RockPaperScissorsSteps
-- name    : Csg_RockPaperScissorsSteps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:43:07.512121+00:00
-- url     : https://prove2.me/theorems/0313a374-7772-4c52-abe4-686273662b03
-- title:
--   Rock Paper Scissors Steps
-- statement:
--   Definitions and structural lemmas for Rock Paper Scissors Steps, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
set_option autoImplicit true
namespace Csg
noncomputable def rpsCSGSteps : CSG RPSState RPSAction RPSAction where
  K := rpsK
  r := fun _ _ _ => 1
noncomputable def rpsStepsStep (v : RPSState → ℝ) (s : RPSState) : ℝ :=
  if s = RPSState.win1 ∨ s = RPSState.win2 then 0 else rpsCSGSteps.stageValue s v
noncomputable def rpsSteps : RPSState → ℝ
  | .win1 => 0
  | .win2 => 0
  | .initial => 2
  | .draw => 3
end Csg


