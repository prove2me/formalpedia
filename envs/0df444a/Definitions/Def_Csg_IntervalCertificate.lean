-- Prove2me | Definitions.Def_Csg_IntervalCertificate
-- name    : Csg_IntervalCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:49:33.943917+00:00
-- url     : https://prove2.me/theorems/f07908ef-eb39-4369-a3b4-cffc49304730
-- title:
--   Interval Certificate
-- statement:
--   Definitions and structural lemmas for Interval Certificate, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntervalCertificate.lean

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_SafetyOp
set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
end CSG
end Csg


