-- Prove2me | Definitions.Def_RequestProject_ThreeAgentTheorem
-- name    : RequestProject_ThreeAgentTheorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:45:42.178545+00:00
-- url     : https://prove2.me/theorems/f69bd070-f69c-45b1-be9a-e73002e0c91a
-- title:
--   Three Agent Theorem
-- statement:
--   Definitions and structural lemmas for Three Agent Theorem, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentTheorem.lean

import Mathlib
import Definitions.Def_RequestProject_PreliminaryPhase
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
end FairSelling


