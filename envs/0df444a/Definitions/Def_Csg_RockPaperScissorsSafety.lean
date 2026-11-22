-- Prove2me | Definitions.Def_Csg_RockPaperScissorsSafety
-- name    : Csg_RockPaperScissorsSafety
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:52:24.362798+00:00
-- url     : https://prove2.me/theorems/b7bee231-d66b-4da5-baa6-9b28e8d9bc4f
-- title:
--   Rock Paper Scissors Safety
-- statement:
--   Definitions and structural lemmas for Rock Paper Scissors Safety, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSafety.lean

import Definitions.Def_Csg_SafetyCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
set_option autoImplicit true
namespace Csg
abbrev rpsSafeUnresolved : RPSState → Prop := fun s => s ≠ .win1 ∧ s ≠ .win2
noncomputable def rpsVStarSafety : RPSState → Set.Icc (0 : ℝ) 1 :=
  fun _ => ⟨0, by norm_num, by norm_num⟩
end Csg


