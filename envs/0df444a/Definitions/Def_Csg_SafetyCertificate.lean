-- Prove2me | Definitions.Def_Csg_SafetyCertificate
-- name    : Csg_SafetyCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:49:01.116779+00:00
-- url     : https://prove2.me/theorems/3809e02a-cc71-4f73-8151-d52bfc7c5bdf
-- title:
--   Safety Certificate
-- statement:
--   Definitions and structural lemmas for Safety Certificate, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SafetyCertificate.lean

import Definitions.Def_Csg_SafetyOp
set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
end CSG
end Csg


