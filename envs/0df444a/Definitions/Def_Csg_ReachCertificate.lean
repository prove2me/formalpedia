-- Prove2me | Definitions.Def_Csg_ReachCertificate
-- name    : Csg_ReachCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:48:45.818744+00:00
-- url     : https://prove2.me/theorems/6fd8c7b4-a835-4caa-8fb9-b29d5b4ee0c7
-- title:
--   Reach Certificate
-- statement:
--   Definitions and structural lemmas for Reach Certificate, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachCertificate.lean

import Definitions.Def_Csg_ReachOp
set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
end CSG
end Csg


