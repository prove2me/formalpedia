-- Prove2me | Definitions.Def_Csg_CsgMonotone
-- name    : Csg_CsgMonotone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:41:49.236285+00:00
-- url     : https://prove2.me/theorems/d5d6392c-3650-4720-82c0-5dea23716747
-- title:
--   Csg Monotone
-- statement:
--   Definitions and structural lemmas for Csg Monotone, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean

import Definitions.Def_Csg_Basic
set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
end CSG
end Csg


