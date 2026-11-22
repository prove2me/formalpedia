-- Prove2me | Definitions.Def_Csg_RewardUntilCertificate
-- name    : Csg_RewardUntilCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:41:53.359254+00:00
-- url     : https://prove2.me/theorems/24ae4a57-c56a-4ef3-802e-6b866b09c6ba
-- title:
--   Reward Until Certificate
-- statement:
--   Definitions and structural lemmas for Reward Until Certificate, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RewardUntilCertificate.lean

import Definitions.Def_Csg_Basic
set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
noncomputable def rewardUntilStep (goal : S → Prop) [DecidablePred goal] (v : S → ℝ) (s : S) : ℝ :=
  if goal s then 0 else C.stageValue s v
end CSG
end Csg


