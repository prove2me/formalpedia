-- Prove2me | Definitions.Def_Csg_BackwardInduction
-- name    : Csg_BackwardInduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:41:48.636003+00:00
-- url     : https://prove2.me/theorems/b1aa548f-f7b3-4b48-8e3f-44155b700992
-- title:
--   Backward Induction
-- statement:
--   Definitions and structural lemmas for Backward Induction, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BackwardInduction.lean

import Definitions.Def_Csg_Basic
set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
noncomputable def bwInd (rFin : S → ℝ) : ℕ → S → ℝ
  | 0 => rFin
  | n + 1 => fun s => C.stageValue s (bwInd rFin n)
end CSG
end Csg


