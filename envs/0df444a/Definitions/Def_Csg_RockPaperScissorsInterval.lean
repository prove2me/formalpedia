-- Prove2me | Definitions.Def_Csg_RockPaperScissorsInterval
-- name    : Csg_RockPaperScissorsInterval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:52:30.879839+00:00
-- url     : https://prove2.me/theorems/0be9a4d7-b50d-4f37-96eb-9551dfcb3698
-- title:
--   Rock Paper Scissors Interval
-- statement:
--   Definitions and structural lemmas for Rock Paper Scissors Interval, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsInterval.lean

import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
set_option autoImplicit true
namespace Csg
noncomputable def rpsLo : RPSState → Set.Icc (0 : ℝ) 1
  | .win1 => ⟨0, by norm_num, by norm_num⟩
  | .win2 => ⟨1, by norm_num, by norm_num⟩
  | .initial => ⟨1 / 3, by norm_num, by norm_num⟩
  | .draw => ⟨1 / 3, by norm_num, by norm_num⟩
noncomputable def rpsHi : RPSState → Set.Icc (0 : ℝ) 1
  | .win1 => ⟨0, by norm_num, by norm_num⟩
  | .win2 => ⟨1, by norm_num, by norm_num⟩
  | .initial => ⟨2 / 3, by norm_num, by norm_num⟩
  | .draw => ⟨2 / 3, by norm_num, by norm_num⟩
end Csg


