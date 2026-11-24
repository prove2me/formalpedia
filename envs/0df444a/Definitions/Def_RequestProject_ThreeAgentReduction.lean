-- Prove2me | Definitions.Def_RequestProject_ThreeAgentReduction
-- name    : RequestProject_ThreeAgentReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:04:39.488399+00:00
-- url     : https://prove2.me/theorems/ebefb1a2-16bf-4eda-96b1-1b594f8430bd
-- title:
--   Three Agent Reduction
-- statement:
--   Definitions and structural lemmas for Three Agent Reduction, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentReduction.lean

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
end FairSelling


