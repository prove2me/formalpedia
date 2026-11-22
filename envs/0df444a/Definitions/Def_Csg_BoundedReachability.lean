-- Prove2me | Definitions.Def_Csg_BoundedReachability
-- name    : Csg_BoundedReachability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:41:52.736001+00:00
-- url     : https://prove2.me/theorems/d8e2372e-26bc-4a6c-a23c-69b3ba438a59
-- title:
--   Bounded Reachability
-- statement:
--   Definitions and structural lemmas for Bounded Reachability, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BoundedReachability.lean

import Definitions.Def_Csg_Basic
set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
noncomputable def reachBounded (goal : S → Prop) [DecidablePred goal] : ℕ → S → ℝ
  | 0 => fun s => if goal s then 1 else 0
  | k + 1 => fun s => if goal s then 1 else C.stageValue s (reachBounded goal k)
end CSG
end Csg


