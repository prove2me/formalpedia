-- Prove2me | Definitions.Def_Csg_RockPaperScissorsUntil
-- name    : Csg_RockPaperScissorsUntil
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:52:25.844258+00:00
-- url     : https://prove2.me/theorems/436422a8-bfb5-48b1-8131-ae9b7f24ac40
-- title:
--   Rock Paper Scissors Until
-- statement:
--   Definitions and structural lemmas for Rock Paper Scissors Until, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
set_option autoImplicit true
namespace Csg
abbrev rpsSafeNotWin1 : RPSState → Prop := fun s => s ≠ RPSState.win1
end Csg


