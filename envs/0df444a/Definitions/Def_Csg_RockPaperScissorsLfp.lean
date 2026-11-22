-- Prove2me | Definitions.Def_Csg_RockPaperScissorsLfp
-- name    : Csg_RockPaperScissorsLfp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:51:00.021802+00:00
-- url     : https://prove2.me/theorems/1f0da2b8-1cfb-4851-ba48-65892e58c049
-- title:
--   Rock Paper Scissors Lfp
-- statement:
--   Definitions and structural lemmas for Rock Paper Scissors Lfp, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsLfp.lean

import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero


set_option autoImplicit true
namespace Csg
theorem rpsR_zero : ∀ s a1 a2, rpsCSG.r s a1 a2 = 0 := by
  intro s a1 a2
  simp [rpsCSG, rpsR]
noncomputable def rpsVStar : RPSState → Set.Icc (0 : ℝ) 1
  | .win1 => ⟨0, by norm_num, by norm_num⟩
  | .win2 => ⟨1, by norm_num, by norm_num⟩
  | .initial => ⟨1 / 2, by norm_num, by norm_num⟩
  | .draw => ⟨1 / 2, by norm_num, by norm_num⟩
end Csg


